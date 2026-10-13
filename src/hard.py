import sys, os, json, time, pathlib, itertools, hashlib, threading
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import benc, run

LOCK = threading.Lock()

def clause_sha(cls):
    return hashlib.sha256(''.join(' '.join(map(str, c)) + ' 0\n' for c in cls).encode()).hexdigest()

def write_cnf(path, nv, cls, extra):
    with open(path, 'w') as fh:
        fh.write('p cnf %d %d\n' % (nv, len(cls) + len(extra)))
        fh.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in cls))
        fh.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in extra))

def build(T):
    a = benc.parse_args(['--kw', T['kw'], '--kb', T['kb']] + T['enc_args'] + ['-o', '/dev/null'])
    return benc.build_from_args(a)

def chk_cubes(e, K):
    x = 1 - e.col(K)
    return [[v] for s, v in sorted(e.A[K + 1][x].items())]

def caps_cubes(e):
    m = e.cap if e.capmode != 'any' else e.n
    out = []
    for w in range(0, m + 1):
        for S in itertools.combinations(range(e.n), w):
            out.append(([e.CAP[t] if t in S else -e.CAP[t] for t in range(e.n)], list(S)))
    return out

def next_chk(node, n):
    anchor = node['anchor']
    used = set(node.get('chk_used', []))
    order = [anchor - 1]
    for d in range(1, n + 1):
        order += [anchor - 1 + d, anchor - 1 - d]
    for K in order:
        if 0 <= K <= n - 1 and K not in used:
            return K
    return None

def save(work, T):
    tmp = work / 'tree.json.tmp'
    json.dump(T, open(tmp, 'w'))
    os.replace(tmp, work / 'tree.json')

def verified(T, nid):
    nd = T['nodes'][nid]
    if nd['status'] == 'UNSAT_VERIFIED':
        return True
    sp = nd.get('split')
    if sp and sp.get('cover') == 'UNSAT_VERIFIED':
        return all(verified(T, c) for c in sp['children'])
    return False

def cmd_init(work, kw, kb, enc_args):
    work.mkdir(parents=True, exist_ok=True)
    if (work / 'tree.json').exists():
        print('exists; not overwritten'); return
    T = {'kw': kw, 'kb': kb, 'enc_args': enc_args or ['-n', '22', '--cap', '1'], 'nodes': {},
         'encoder_sha256': run.sha(HERE / 'benc.py'), 'hard_sha256': run.sha(HERE / 'hard.py')}
    e = build(T)
    T['base_sha256'] = clause_sha(e.cls)
    T['n'], T['nv'], T['nc'] = e.n, e.nv, len(e.cls)
    T['nodes']['r'] = {'units': [], 'kind': 'root', 'status': 'PENDING', 'depth': 0, 'attempts': [],
                       'anchor': e.n // 2, 'chk_used': []}
    save(work, T)
    print(json.dumps({'kw': kw, 'kb': kb, 'nv': e.nv, 'nc': len(e.cls)}))

def make_split(T, e, nid):
    nd = T['nodes'][nid]
    kids = []
    if nd['kind'] == 'root':
        spec = 'caps'
        for i, (u, S) in enumerate(caps_cubes(e)):
            t = min([s for s in S if s >= 1], default=None)
            kids.append(('%s/%d' % (nid, i), {'units': u, 'kind': 'caps', 'caps': S,
                                              'anchor': t if t is not None else e.n // 2, 'chk_used': []}))
    else:
        K = next_chk(nd, e.n)
        if K is None:
            return False
        spec = 'chk:%d' % K
        for i, (l,) in enumerate(chk_cubes(e, K)):
            kids.append(('%s/%d' % (nid, i), {'units': nd['units'] + [l], 'kind': 'chk', 'anchor': nd['anchor'],
                                              'chk_used': nd.get('chk_used', []) + [K]}))
    for cid, c in kids:
        c.update({'status': 'PENDING', 'depth': nd['depth'] + 1, 'attempts': []})
        T['nodes'][cid] = c
    nd['split'] = {'spec': spec, 'children': [cid for cid, _ in kids], 'cover': 'PENDING'}
    nd['status'] = 'SPLIT'
    return True

def cmd_run(work, total, jobs, t1, t2, troot, tmin, opts, presplit=None):
    T = json.load(open(work / 'tree.json'))
    e = build(T)
    assert clause_sha(e.cls) == T['base_sha256'], 'encoder output differs from init'
    meta = e.meta()
    t_end = time.time() + total
    log = open(work / 'log.jsonl', 'a')
    scratch = pathlib.Path(os.environ.get('HARD_SCRATCH', str(work / 'scratch'))) / (T['kw'] + T['kb'])
    scratch.mkdir(parents=True, exist_ok=True)
    running = set()

    def nominal(nd):
        if nd['kind'] == 'root':
            return troot
        return t1 if nd['kind'] == 'caps' else t2

    def pick():
        left = t_end - time.time()

        for nid, nd in T['nodes'].items():
            sp = nd.get('split')
            if sp and sp['cover'] == 'PENDING' and ('cover', nid) not in running and left > 90:
                return ('cover', nid, int(min(120, left - 30)))

        pri = [p for p in os.environ.get('HARD_PRIORITY', '').split(',') if p]
        cand = sorted((nd['depth'] if not any(nid.startswith(p) for p in pri) else -1, nid)
                      for nid, nd in T['nodes'].items()
                      if nd['status'] == 'PENDING' and ('leaf', nid) not in running)
        for _, nid in cand:
            nd = T['nodes'][nid]
            nom = nominal(nd)
            if nd['kind'] == 'root' and nom <= 0:
                continue
            if left >= nom + 25:
                return ('leaf', nid, nom)
            if left >= tmin + 25:
                return ('leaf', nid, int(left - 25))
            return None
        return None

    def job(item):
        kind, nid, tmo = item
        nd = T['nodes'][nid]
        d = scratch / (nid.replace('/', '_') + ('_cover' if kind == 'cover' else ''))
        d.mkdir(exist_ok=True)
        cnf = d / 'f.cnf'
        if kind == 'leaf':
            extra = [[u] for u in nd['units']]
        else:
            extra = [[u] for u in nd['units']] + [[-l for l in T['nodes'][c]['units']] for c in nd['split']['children']]
        write_cnf(cnf, e.nv, e.cls, extra)
        rec = run.solve(cnf, d, tmo, True, opts)
        cnf.unlink(missing_ok=True)
        import shutil
        shutil.rmtree(d, ignore_errors=True)
        r = {'node': nid, 'kind': kind, 'status': rec['status'], 'seconds': round(rec['seconds'], 2),
             'timeout': tmo, 'cnf_sha256': rec['cnf_sha256'], 'proof_sha256': rec.get('proof_sha256'),
             'proof_bytes': rec.get('proof_bytes'), 'chk1_exit': rec.get('chk1_exit'), 'chk2_exit': rec.get('chk2_exit'), 'chk3_exit': rec.get('chk3_exit'),
             'chk1_out': (rec.get('chk1_out') or '').strip()[:80], 'chk2_out': (rec.get('chk2_out') or '').strip()[:160],
             'opts': list(opts), 'time': time.strftime('%Y-%m-%dT%H:%M:%S')}
        if rec['status'] == 'SAT':
            rep = run.check_sat(meta, rec['model'])
            r['replay'] = {k: rep[k] for k in ('ok', 'fen', 'san', 'captures', 'plies', 'verified')}
        return item, r

    def apply(item, r):
        kind, nid, tmo = item
        nd = T['nodes'][nid]
        log.write(json.dumps(r) + '\n'); log.flush()
        if kind == 'cover':
            nd['split']['cover'] = r['status']
            nd['split']['cover_rec'] = r
            return
        nd['attempts'].append({k: r[k] for k in ('status', 'seconds', 'timeout')})
        if r['status'] == 'UNSAT_VERIFIED':
            nd['status'] = 'UNSAT_VERIFIED'
            nd['rec'] = r
        elif r['status'] in ('SAT', 'SAT_REPLAY_FAILED'):
            nd['status'] = r['status']
            nd['rec'] = r
            T['SAT'] = r
        elif r['status'] == 'UNKNOWN' and tmo >= 0.9 * nominal(nd):
            if not make_split(T, e, nid):
                nd['status'] = 'UNKNOWN_FINAL'
        elif r['status'] == 'UNSAT_UNCERTIFIED':
            nd['status'] = 'PENDING'
    def presplit_scan():

        if not presplit:
            return
        for nid in list(T['nodes']):
            nd = T['nodes'][nid]
            ts = [x for x in nd.get('caps') or [] if x >= 1]
            if nd['kind'] == 'caps' and nd['status'] == 'PENDING' and ts and \
                    presplit[0] <= min(ts) <= presplit[1] and ('leaf', nid) not in running:
                make_split(T, e, nid)
        save(work, T)
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = set()
        while True:
            with LOCK:
                presplit_scan()
                if 'SAT' in T:
                    break
                while len(futs) < jobs:
                    it = pick()
                    if it is None:
                        break
                    running.add((it[0], it[1]))
                    futs.add(ex.submit(job, it))
            if not futs:
                if root_done(T) or time.time() > t_end - 60:
                    break

                with LOCK:
                    r0 = T['nodes']['r']
                    if r0['status'] == 'PENDING' and troot <= 0:
                        make_split(T, e, 'r'); save(work, T); continue
                break
            done, futs = wait(futs, return_when=FIRST_COMPLETED)
            for f in done:
                item, r = f.result()
                with LOCK:
                    running.discard((item[0], item[1]))
                    apply(item, r)
                    save(work, T)
    log.close()
    cmd_status(work)

def root_done(T):
    return verified(T, 'r')

def cmd_status(work):
    T = json.load(open(work / 'tree.json'))
    from collections import Counter
    c = Counter(nd['status'] for nd in T['nodes'].values())
    covers = Counter(nd['split']['cover'] for nd in T['nodes'].values() if nd.get('split'))
    print(json.dumps({'placement': T['kw'] + T['kb'], 'VERIFIED': verified(T, 'r'), 'nodes': dict(c),
                      'covers': dict(covers), 'SAT': T.get('SAT') is not None}))

if __name__ == '__main__':
    argv = sys.argv[1:]
    enc = []
    if '--' in argv:
        i = argv.index('--')
        argv, enc = argv[:i], argv[i + 1:]
    work, cmd = pathlib.Path(argv[0]), argv[1]

    def opt(name, default):
        return int(argv[argv.index(name) + 1]) if name in argv else default
    if cmd == 'init':
        cmd_init(work, argv[2], argv[3], enc)
    elif cmd == 'run':
        opts = [o for o in os.environ.get('HARD_OPTS', '--unsat').split(',') if o]
        ps = None
        if '--presplit' in argv:
            ps = tuple(int(x) for x in argv[argv.index('--presplit') + 1].split('-'))
        cmd_run(work, int(argv[2]), int(argv[3]), opt('--t1', 240), opt('--t2', 240), opt('--root', 0),
                opt('--min', 60), opts, ps)
    elif cmd == 'status':
        cmd_status(work)
