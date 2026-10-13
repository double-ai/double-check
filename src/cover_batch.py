import sys, os, json, time, pathlib, subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import benc, run

def reps():
    out = []
    for w in range(64):
        for b in range(64):
            if max(abs(w % 8 - b % 8), abs(w // 8 - b // 8)) <= 1:
                continue
            if (w, b) <= (w ^ 7, b ^ 7):
                out.append((w, b))
    return out

def load(work):
    st = json.load(open(work / 'state.json'))
    man = {}
    if (work / 'manifest.jsonl').exists():
        for line in open(work / 'manifest.jsonl'):
            r = json.loads(line)
            man[r['idx']] = r
    return st, man

def main():
    argv = sys.argv[1:]
    enc = []
    if '--' in argv:
        i = argv.index('--')
        argv, enc = argv[:i], argv[i + 1:]
    work, cmd = pathlib.Path(argv[0]), argv[1]
    if cmd == 'init':
        work.mkdir(parents=True, exist_ok=True)
        R = reps()
        st = {'enc_args': enc, 'reps': R, 'n_reps': len(R),
              'encoder_sha256': run.sha(HERE / 'benc.py')}
        json.dump(st, open(work / 'state.json', 'w'))
        print(json.dumps({'n_reps': st['n_reps']}))
        return
    st, man = load(work)
    if cmd == 'status':
        from collections import Counter
        c = Counter(man.get(i, {}).get('status', 'PENDING') for i in range(st['n_reps']))
        secs = sorted(((r['seconds'], i) for i, r in man.items()), reverse=True)[:5]
        print(json.dumps({'counts': dict(c), 'cpu_s': round(sum(r['seconds'] for r in man.values()), 1),
                          'slowest': [(round(s, 1), benc.sqn(st['reps'][i][0]) + benc.sqn(st['reps'][i][1])) for s, i in secs]}))
        return
    total, per, jobs = int(argv[2]), int(argv[3]), int(argv[4])
    lrat = '--lrat' in argv
    lo, hi = 0, st['n_reps'] - 1
    if '--range' in argv:
        lo, hi = map(int, argv[argv.index('--range') + 1].split('-'))
    stride = int(argv[argv.index('--stride') + 1]) if '--stride' in argv else 1
    done_ok = ('UNSAT_VERIFIED', 'SAT') if lrat else ('UNSAT_VERIFIED', 'SAT', 'UNSAT_UNCERTIFIED')
    todo = [i for i in range(lo, hi + 1, stride) if man.get(i, {}).get('status') not in done_ok
            and man.get(i, {}).get('timeout', 0) < per]
    t_end = time.time() + total
    out = open(work / 'manifest.jsonl', 'a')

    def one(i):
        left = t_end - time.time()
        if left < min(per, 60) + 10:
            return None
        tmo = int(min(per, left - 10))
        w, b = st['reps'][i]
        d = work / ('p%04d' % i)
        d.mkdir(exist_ok=True)
        a = benc.parse_args(['--kw', benc.sqn(w), '--kb', benc.sqn(b)] + st['enc_args'] + ['-o', str(d / 'f.cnf')])
        e = benc.build_from_args(a)
        e.dimacs(str(d / 'f.cnf'))
        rec = run.solve(d / 'f.cnf', d, tmo, lrat, [o for o in os.environ.get('COVER_OPTS', '').split(',') if o])
        r = {'idx': i, 'kw': benc.sqn(w), 'kb': benc.sqn(b), 'status': rec['status'],
             'seconds': round(rec['seconds'], 2), 'timeout': tmo, 'cnf_sha256': rec['cnf_sha256'], 'lrat': lrat}
        if lrat:
            r.update({k: rec.get(k) for k in ('proof_bytes', 'proof_sha256', 'chk1_exit', 'chk2_exit', 'chk3_exit')})
            r['chk1_out'] = (rec.get('chk1_out') or '').strip()[:60]
        if rec['status'] == 'SAT':
            rep = run.check_sat(e.meta(), rec['model'])
            r['replay'] = {k: rep[k] for k in ('ok', 'fen', 'san', 'captures', 'plies', 'verified')}
        (d / 'f.cnf').unlink(missing_ok=True)
        return r
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        it = iter(todo)
        futs = {}
        for _ in range(jobs):
            i = next(it, None)
            if i is not None:
                futs[ex.submit(one, i)] = i
        while futs:
            f = next(as_completed(list(futs)))
            futs.pop(f)
            r = f.result()
            if r is not None:
                out.write(json.dumps(r) + '\n'); out.flush()
            if time.time() < t_end - 70:
                j = next(it, None)
                if j is not None:
                    futs[ex.submit(one, j)] = j
    out.close()
    main_status = subprocess.run([sys.executable, __file__, str(work), 'status'], capture_output=True, text=True)
    print(main_status.stdout.strip())

if __name__ == '__main__':
    main()
