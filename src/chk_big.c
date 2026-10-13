#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>
#include <errno.h>

typedef struct Clause {
  int64_t id;
  int size;
  int *lits;
  int deleted;
} Clause;

static Clause **by_id = 0;
static int64_t id_cap = 0;

static int vars = 0;
static int8_t *val = 0;
static int *trail = 0;
static int trail_len = 0, trail_cap = 0;

static int64_t last_added_id = 0;

static const char *g_cnf_name = 0, *g_lrat_name = 0;
static long long g_line = 0;

static void die(int status, const char *msg) {
  fprintf(stderr, "lrat_check: %s: %lld: %s\n",
          g_lrat_name ? g_lrat_name : "?", g_line, msg);
  exit(status);
}

static void die_cnf(const char *msg) {
  fprintf(stderr, "lrat_check: %s: %s\n", g_cnf_name ? g_cnf_name : "?", msg);
  exit(1);
}

static void ensure_var(int v) {
  if (v < vars) return;
  int nv = vars ? vars : 1024;
  while (nv <= v) nv *= 2;
  int8_t *nval = (int8_t *)realloc(val, (size_t)nv);
  if (!nval) { fprintf(stderr, "lrat_check: out of memory\n"); exit(2); }
  memset(nval + vars, 0, (size_t)(nv - vars));
  val = nval; vars = nv;
}

static Clause *find_clause(int64_t id) {
  if (id <= 0 || id >= id_cap) return 0;
  return by_id[id];
}

static Clause *new_clause(int64_t id, int size, int *lits) {
  Clause *c = (Clause *)malloc(sizeof(Clause));
  if (!c) { fprintf(stderr, "lrat_check: out of memory\n"); exit(2); }
  c->id = id; c->size = size; c->deleted = 0;
  c->lits = (int *)malloc((size_t)(size ? size : 1) * sizeof(int));
  if (!c->lits) { fprintf(stderr, "lrat_check: out of memory\n"); exit(2); }
  memcpy(c->lits, lits, (size_t)size * sizeof(int));
  return c;
}

static int tokenize(char *s, char **tok, int maxtok) {
  int n = 0;
  char *p = s;
  while (*p) {
    while (*p && isspace((unsigned char)*p)) p++;
    if (!*p) break;
    if (n >= maxtok) return -1;
    tok[n++] = p;
    while (*p && !isspace((unsigned char)*p)) p++;
    if (*p) *p++ = 0;
  }
  return n;
}

static int read_line(char **buf, size_t *cap, FILE *f) {
  long long n = 0;
  for (;;) {
    if (getline(buf, cap, f) < 0) return 0;
    g_line++; n++;

    size_t len = strlen(*buf);
    while (len && ((*buf)[len-1] == '\n' || (*buf)[len-1] == '\r')) (*buf)[--len] = 0;

    if (len == 0) continue;
    if ((*buf)[0] == 'c') continue;
    return 1;
  }
}

static void load_dimacs(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) { fprintf(stderr, "lrat_check: cannot open %s\n", path); exit(2); }
  char *buf = 0; size_t cap = 0;
  char *tok[4096];
  int nvars = -1, ncls = -1;
  int64_t id = 0;
  while (read_line(&buf, &cap, f)) {
    char *s = buf;
    while (*s && isspace((unsigned char)*s)) s++;
    if (*s == 'c') continue;
    int nt = tokenize(s, tok, 4096);
    if (nt < 0) die_cnf("DIMACS line too long");
    if (nt == 0) continue;
    if (tok[0][0] == 'p') {
      if (nt < 4 || strcmp(tok[1], "cnf") != 0)
        die_cnf("bad 'p' line, expected 'p cnf V C'");
      nvars = atoi(tok[2]); ncls = atoi(tok[3]);
      if (nvars < 0 || ncls < 0) die_cnf("bad 'p cnf' header");

      ensure_var(nvars + 1);
      continue;
    }
    if (nvars < 0) die_cnf("no 'p cnf' header");

    id++;
    if (id > ncls) die_cnf("more clauses than declared in 'p cnf' header");
    int len = 0;
    int t = 0;

    int term = 0;
    static int *biglits = 0; static int bigcap = 0;
    for (t = 0; t < nt; t++) {
      if (tok[t][0] == '0' ) { term = t; break; }
    }
    if (!term && nt > 0 && tok[nt-1][0] == '0') term = nt-1;
    if (!term && !(nt>0 && tok[nt-1][0]=='0')) {
      if (nt==0) continue;
      die_cnf("clause not terminated by 0");
    }
    (void)term;
    for (t = 0; t < nt; t++) {
      if (tok[t][0] == '0') break;
      long v = atol(tok[t]);
      if (v == 0) break;
      if (v > nvars || v < -nvars) { char m[128]; snprintf(m,sizeof m,"literal %ld exceeds declared variables %d", v, nvars); die_cnf(m); }
      if (len >= bigcap) { bigcap = bigcap ? bigcap*2 : 64; biglits = (int*)realloc(biglits, bigcap*sizeof(int)); }
      biglits[len++] = (int)v;
    }
    Clause *c = new_clause(id, len, biglits);
    if (id >= id_cap) {
      int64_t ncap = id_cap ? id_cap : 1024;
      while (ncap <= id) ncap *= 2;
      by_id = (Clause **)realloc(by_id, (size_t)ncap * sizeof(Clause*));
      memset(by_id + id_cap, 0, (size_t)(ncap - id_cap) * sizeof(Clause*));
      id_cap = ncap;
    }
    by_id[id] = c;
    last_added_id = id;
  }
  fclose(f);
  if (id != ncls) { char m[128]; snprintf(m,sizeof m,"DIMACS declares %d clauses but %lld found", ncls, (long long)id); die_cnf(m); }
}

static inline int lit_false(int lit) {
  int v = lit > 0 ? lit : -lit;
  return lit > 0 ? (val[v] == 2) : (val[v] == 1);
}

static inline void falsify(int lit) {
  int v = lit > 0 ? lit : -lit;
  if (val[v] == 0) {
    if (trail_len >= trail_cap) {
      trail_cap *= 2; trail = (int *)realloc(trail, (size_t)trail_cap * sizeof(int));
      if (!trail) { fprintf(stderr, "lrat_check: out of memory\n"); exit(2); }
    }
    val[v] = lit > 0 ? 2 : 1; trail[trail_len++] = v;
  }
}

static int check_rup(int len, int *lits, const int64_t *hints, int nhints, char *reason, size_t reasonsz) {
  int i;
  for (i = 0; i < len; i++) falsify(lits[i]);
  for (i = 0; i < nhints; i++) {
    int64_t hid = hints[i];
    Clause *c = find_clause(hid);
    if (!c) { snprintf(reason, reasonsz, "hint %lld does not exist", (long long)hid); return 0; }
    if (c->deleted) { snprintf(reason, reasonsz, "hint %lld is deleted", (long long)hid); return 0; }
    int j, unit = 0, unf = 0;
    for (j = 0; j < c->size; j++) {
      if (!lit_false(c->lits[j])) {
        unf++;
        if (unf >= 2) break;
        unit = c->lits[j];
      }
    }
    if (unf == 0) return 1;
    if (unf >= 2) { snprintf(reason, reasonsz, "hint %lld is not unit nor falsified", (long long)hid); return 0; }

    falsify(-unit);
  }
  snprintf(reason, reasonsz, "no falsified clause reached (RUP failed)");
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s <formula.cnf> <proof.lrat>\n", argv[0]);
    return 2;
  }
  g_cnf_name = argv[1]; g_lrat_name = argv[2];
  load_dimacs(argv[1]);
  if (vars == 0) { ensure_var(1); }
  trail_cap = 1 << 16; trail = (int *)malloc((size_t)trail_cap * sizeof(int));
  if (!trail) { fprintf(stderr, "lrat_check: out of memory\n"); exit(2); }

  FILE *f = fopen(argv[2], "r");
  if (!f) { fprintf(stderr, "lrat_check: cannot open %s\n", argv[2]); exit(2); }
  char *buf = 0; size_t cap = 0;
  static char *tok[1<<22];
  int64_t additions = 0, deletions = 0, hints_total = 0, empty_seen = 0;
  int last_was_empty_addition = 0;

  while (read_line(&buf, &cap, f)) {
    last_was_empty_addition = 0;
    int nt = tokenize(buf, tok, 1<<22);
    if (nt < 0) die(1, "proof line too long");
    if (nt == 0) continue;
    if (tok[0][0] == 'c') continue;
    if (tok[0][0] == 'p' && nt >= 2 && strcmp(tok[1],"lrat")==0) continue;
    if (tok[0][0] == 'p') die(1, "unexpected 'p' line in proof");
    errno = 0;
    char *end = 0;
    long long id = strtoll(tok[0], &end, 10);
    if (!end || *end || id <= 0) die(1, "expected a positive clause id at start of line");
    if (nt >= 2 && tok[1][0] == 'd' && tok[1][1] == 0) {

      for (int i = 2; i < nt; i++) {
        if (tok[i][0] == '0') continue;
        long long did = atoll(tok[i]);
        if (did <= 0) die(1, "bad id in deletion line");
        Clause *c = find_clause(did);
        if (!c) { char m[160]; snprintf(m, sizeof m, "deletion: clause %lld does not exist", did); die(1, m); }
        if (c->deleted) { char m[160]; snprintf(m, sizeof m, "deletion: clause %lld already deleted", did); die(1, m); }
        c->deleted = 1;
        deletions++;
      }
      continue;
    }

    if (id != last_added_id + 1) {
      char m[128]; snprintf(m, sizeof m, "addition id %lld, expected %lld (ids must increase by 1)", id, (long long)(last_added_id+1));
      die(1, m);
    }
    static int lits[1<<22]; int len = 0;
    static int64_t hints[1<<22]; int nh = 0;
    int i = 1, seen0 = 0;
    for (; i < nt; i++) {
      if (tok[i][0] == '0') { seen0 = 1; i++; break; }
      long long l = atoll(tok[i]);
      if (l == 0) { seen0 = 1; i++; break; }
      if (l > 2147483647LL || l < -2147483647LL) die(1, "literal out of range");
      if (len >= (1<<22)) { char m[96]; snprintf(m,sizeof m,"clause has more than 4194304 literals"); die(1,m); }
      lits[len++] = (int)l;
    }
    if (!seen0) die(1, "addition line has no literal terminator 0");

    for (int a = 0; a < len; a++) {
      int va = lits[a] > 0 ? lits[a] : -lits[a];
      if (va > vars) ensure_var(va);
      for (int b = 0; b < a; b++) {
        if (lits[b] == lits[a]) { char m[128]; snprintf(m,sizeof m,"duplicate literal %d in addition id %lld", lits[a], id); die(1,m); }
        if (lits[b] == -lits[a]) { char m[128]; snprintf(m,sizeof m,"tautological addition id %lld", id); die(1,m); }
      }
    }

    for (; i < nt; i++) {
      if (tok[i][0] == '0') { seen0 = 2; i++; break; }
      if (nh >= (1<<22)) die(1, "too many hints on one line");
      long long h = atoll(tok[i]);
      if (h < 0) {
        char m[160]; snprintf(m,sizeof m,"negative hint %lld (RAT/ER line): cadical --lrat=true --binary=false emits only RUP lines; RAT hints are not supported", h);
        die(1, m);
      }
      if (h == 0) die(1, "unexpected 0 inside hints");
      hints[nh++] = h;
    }
    if (seen0 != 2) die(1, "addition line has no hint terminator 0");
    hints_total += nh;

    char reason[256]; reason[0] = 0;
    if (!check_rup(len, lits, hints, nh, reason, sizeof reason)) {
      char m[320];
      if (reason[0]) snprintf(m, sizeof m, "RUP check failed for addition id %lld: %s", id, reason);
      else snprintf(m, sizeof m, "RUP check failed for addition id %lld", id);
      die(1, m);
    }

    Clause *c = new_clause(id, len, lits);
    if (id >= id_cap) {
      int64_t ncap = id_cap ? id_cap : 1024;
      while (ncap <= id) ncap *= 2;
      by_id = (Clause **)realloc(by_id, (size_t)ncap * sizeof(Clause*));
      memset(by_id + id_cap, 0, (size_t)(ncap - id_cap) * sizeof(Clause*));
      id_cap = ncap;
    }
    by_id[id] = c;
    last_added_id = id;
    additions++;
    if (len == 0) empty_seen = 1, last_was_empty_addition = 1;

    for (int t = 0; t < trail_len; t++) val[trail[t]] = 0;
    trail_len = 0;
  }
  if (!empty_seen) die(1, "empty clause never derived");
  if (!last_was_empty_addition) die(1, "empty clause is not the final line");
  printf("s VERIFIED formula %s with proof %s: %lld additions, %lld deletions, %lld hints, empty clause derived at the final line\n",
         argv[1], argv[2], (long long)additions, (long long)deletions, (long long)hints_total);
  return 0;
}
