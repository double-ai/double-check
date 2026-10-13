#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using Clause = std::vector<int>;
static void require(bool b, const std::string &msg) { if (!b) throw std::runtime_error(msg); }
int main(int argc, char **argv) {
 try {
  require(argc >= 3 && argc <= 5, "usage: lrat_rup_check CNF PROOF [CHECKPOINT_CNF [active]]");
  const bool active_only = argc == 5;
  if (active_only) require(std::string(argv[4]) == "active", "unknown checkpoint mode");
  std::ifstream cnf(argv[1]), proof(argv[2]);
  require(bool(cnf) && bool(proof), "cannot open input");
  std::unordered_map<int64_t, Clause> db;
  std::vector<Clause> original;
  std::string line;
  int64_t nvar = -1, ncls = -1, last_id = 0;
  Clause pending;
  while (std::getline(cnf, line)) {
   std::istringstream ss(line);
   std::string token;
   if (!(ss >> token) || token == "c") continue;
   if (token == "p") {
    std::string typ; ss >> typ >> nvar >> ncls;
    require(typ == "cnf" && nvar >= 0 && ncls >= 0, "bad DIMACS header");
    continue;
   }
   require(nvar >= 0, "missing DIMACS header");
   ss.clear(); ss.str(line);
   int64_t x;
   while (ss >> x) {
    require(x >= -nvar && x <= nvar, "CNF literal out of range");
    if (x) pending.push_back(int(x));
    else { db.emplace(++last_id, pending); original.push_back(pending); pending.clear(); }
   }
   require(ss.eof(), "bad DIMACS token");
  }
  require(pending.empty() && last_id == ncls, "DIMACS clause count mismatch");

  std::vector<int64_t> stamp(nvar + 1, 0);
  std::vector<int> value(nvar + 1, 0);
  int64_t epoch = 0, adds = 0, dels = 0, lineno = 0;
  bool empty = false;
  auto set_true = [&](int lit) -> bool {
   const int v = std::abs(lit);
   if (stamp[v] == epoch) return value[v] == lit;
   stamp[v] = epoch; value[v] = lit; return true;
  };
  while (std::getline(proof, line)) {
   ++lineno;
   std::istringstream ss(line);
   std::string first, second;
   if (!(ss >> first) || first == "c") continue;
   require(bool(ss >> second), "truncated proof line");
   int64_t id = std::stoll(first);
   require(id > 0, "nonpositive line id");
   if (second == "d") {
    int64_t x; bool zero = false;
    while (ss >> x) {
     if (x == 0) { zero = true; break; }
     require(x > 0, "negative deletion id");

     db.erase(x); ++dels;
    }
    require(zero, "unterminated deletion");
    std::string extra; require(!(ss >> extra), "extra deletion tokens");
    continue;
   }
   require(id > last_id, "addition ids must strictly increase");
   Clause clause;
   int64_t x = std::stoll(second);
   while (x) {
    require(x >= -nvar && x <= nvar, "proof literal out of range");
    clause.push_back(int(x));
    require(bool(ss >> x), "unterminated clause");
   }
   std::vector<int64_t> hints;
   bool zero = false;
   while (ss >> x) {
    if (x == 0) { zero = true; break; }
    require(x > 0, "negative hint: RAT unsupported, not certified");
    hints.push_back(x);
   }
   require(zero, "unterminated hints");
   std::string extra; require(!(ss >> extra), "extra addition tokens");
   ++epoch;
   bool conflict = false;
   for (int lit : clause) if (!set_true(-lit)) conflict = true;
   for (int64_t hint : hints) {
    auto it = db.find(hint);
    require(it != db.end(), "hint references missing/deleted clause");
    if (conflict) continue;
    bool satisfied = false;
    int unit = 0;
    for (int lit : it->second) {
     int v = std::abs(lit);
     if (stamp[v] == epoch) {
      if (value[v] == lit) { satisfied = true; break; }
     } else if (!unit) unit = lit;
     else if (unit != lit) { unit = INT32_MIN; }
    }

    if (satisfied) continue;
    require(unit != INT32_MIN, "hint clause is not unit/conflict");
    if (unit == 0) conflict = true;
    else require(set_true(unit), "internal inconsistent unit");
   }
   require(conflict, "RUP hints do not derive conflict at line " + std::to_string(lineno));
   db.emplace(id, clause); last_id = id; ++adds;
   if (clause.empty()) empty = true;
  }
  if (!empty && argc >= 4) {

   std::vector<int64_t> ids;
   for (const auto &entry : db) if (active_only || entry.first > ncls) ids.push_back(entry.first);
   std::sort(ids.begin(), ids.end());
   std::ofstream out(argv[3]);
   require(bool(out), "cannot write checkpoint");
   out << "p cnf " << nvar << " " << (active_only ? 0 : original.size()) + ids.size() << "\n";
   if (!active_only) for (const auto &c : original) { for (int lit : c) out << lit << " "; out << "0\n"; }
   for (int64_t id : ids) { for (int lit : db.at(id)) out << lit << " "; out << "0\n"; }
   out.close(); require(bool(out), "checkpoint write failed");
   std::cout << "s PREFIX VERIFIED RUP\nc additions " << adds << " deletions " << dels
             << " retained " << ids.size() << "\n";
   return 2;
  }
  require(empty, "proof contains no verified empty-clause addition");
  std::cout << "s VERIFIED RUP\nc additions " << adds << " deletions " << dels << "\n";
  return 0;
 } catch (const std::exception &e) {
  std::cerr << "s NOT VERIFIED\nc " << e.what() << "\n";
  return 1;
 }
}
