import sys, os, json, time, hashlib, subprocess, threading, pathlib, argparse

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import benc

CADICAL = os.environ.get('B1_CADICAL', 'cadical')
CHK1 = os.environ.get('B1_CHK1', 'chk_strict')
CHK2 = os.environ.get('B1_CHK2', 'chk_big')
CHK3 = os.environ.get('B1_CHK3')

def ensure_checkers():
    if not os.access(CHK1, os.X_OK):
        subprocess.run(['g++', '-O2', '-std=c++17', '-o', CHK1, str(HERE / 'chk_strict.cpp')], check=True)
    if not os.access(CHK2, os.X_OK):
        subprocess.run(['gcc', '-O2', '-o', CHK2, str(HERE / 'chk_big.c')], check=True)

def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def parse_model(text):
    lits = set()
    for line in text.splitlines():
        if line.startswith('v '):
            for x in line[2:].split():
                x = int(x)
                if x:
                    lits.add(x)
    return lits

def solve(cnf, out, timeout, lrat=False, extra_opts=()):
    out = pathlib.Path(out)
    out.mkdir(parents=True, exist_ok=True)
    rec = {'cnf': str(cnf), 'cnf_sha256': sha(cnf), 'timeout': timeout, 'lrat': lrat}
    t0 = time.time()
    if not lrat:
        cmd = [CADICAL, '-t', str(timeout)] + list(extra_opts) + [str(cnf)]
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        rec['solver_exit'] = p.returncode
        rec['seconds'] = time.time() - t0
        (out / 'solver.log').write_text(p.stdout if p.returncode != 10 else '\n'.join(
            l for l in p.stdout.splitlines() if not l.startswith('v ')))
        rec['status'] = {10: 'SAT', 20: 'UNSAT_UNCERTIFIED'}.get(p.returncode, 'UNKNOWN')
        if p.returncode == 10:
            rec['model'] = parse_model(p.stdout)
        return rec
    ensure_checkers()
    import tempfile
    fdir = pathlib.Path(tempfile.mkdtemp(prefix='lratfifo_', dir='/tmp'))
    raw, f1, f2, f3 = fdir / 'raw.fifo', fdir / 'c1.fifo', fdir / 'c2.fifo', fdir / 'c3.fifo'
    fs = (raw, f1, f2, f3) if CHK3 else (raw, f1, f2)
    for f in fs:
        if f.exists():
            f.unlink()
        os.mkfifo(f)
    st = {'bytes': 0, 'err': None}
    h = hashlib.sha256()

    def pump():
        try:
            with open(raw, 'rb') as src, open(f1, 'wb') as d1, open(f2, 'wb') as d2, (open(f3, 'wb') if CHK3 else open(os.devnull, 'wb')) as d3:
                while True:
                    b = src.read(1 << 20)
                    if not b:
                        break
                    h.update(b)
                    st['bytes'] += len(b)
                    d1.write(b)
                    d2.write(b)
                    d3.write(b)
        except Exception as ex:
            st['err'] = repr(ex)
    l1, l2, l3 = open(out / 'chk1.log', 'w'), open(out / 'chk2.log', 'w'), open(out / 'chk3.log', 'w')
    c1 = subprocess.Popen([CHK1, str(cnf), str(f1)], stdout=l1, stderr=subprocess.STDOUT)
    c2 = subprocess.Popen([CHK2, str(cnf), str(f2)], stdout=l2, stderr=subprocess.STDOUT)
    c3 = subprocess.Popen([CHK3, str(cnf), str(f3)], stdout=l3, stderr=subprocess.STDOUT) if CHK3 else None
    th = threading.Thread(target=pump, daemon=True)
    th.start()
    cmd = [CADICAL, '--lrat=true', '--binary=false', '-t', str(timeout)] + list(extra_opts) + [str(cnf), str(raw)]
    with open(out / 'solver.log', 'w') as sl:
        sp = subprocess.Popen(cmd, stdout=sl, stderr=subprocess.STDOUT)
        try:
            sr = sp.wait(timeout=timeout + 60)
        except subprocess.TimeoutExpired:
            sp.kill()
            sr = -9
    th.join(timeout=180)
    try:
        r1 = c1.wait(timeout=180)
        r2 = c2.wait(timeout=180)
        r3 = c3.wait(timeout=180) if c3 else None
    except subprocess.TimeoutExpired:
        c1.kill(); c2.kill()
        if c3: c3.kill()
        r1 = r2 = r3 = -9
    l1.close(); l2.close(); l3.close()
    for f in fs:
        f.unlink(missing_ok=True)
    try:
        fdir.rmdir()
    except OSError:
        pass
    rec.update({'solver_exit': sr, 'seconds': time.time() - t0, 'proof_bytes': st['bytes'],
                'proof_sha256': h.hexdigest(), 'pump_error': st['err'],
                'chk1_exit': r1, 'chk2_exit': r2, 'chk3_exit': r3, 'chk3': CHK3,
                'chk1_out': (out / 'chk1.log').read_text()[-300:], 'chk2_out': (out / 'chk2.log').read_text()[-300:],
                'solver_command': cmd})
    if sr == 20:
        ok1 = r1 == 0 and 's VERIFIED' in rec['chk1_out']
        ok2 = r2 == 0 and (CHK3 is None or r3 == 0)
        rec['status'] = 'UNSAT_VERIFIED' if (ok1 and ok2 and st['err'] is None) else 'UNSAT_UNCERTIFIED'
    elif sr == 10:
        rec['status'] = 'SAT'
        txt = (out / 'solver.log').read_text()
        rec['model'] = parse_model(txt)
        (out / 'solver.log').write_text('\n'.join(l for l in txt.splitlines() if not l.startswith('v ')))
    else:
        rec['status'] = 'UNKNOWN'
    return rec

def check_sat(meta, model, bound_caps=None):
    fen, moves = benc.decode(meta, model)
    rep = benc.replay(fen, moves)
    rep['fen'] = fen
    rep['uci'] = moves
    ok = rep['ok'] and rep['plies'] == meta['n']
    if bound_caps is not None:
        ok = ok and bound_caps(rep['captures'])
    rep['verified'] = ok
    return rep

def main():
    argv = sys.argv[1:]
    if '--' in argv:
        i = argv.index('--')
        mine, enc_args = argv[:i], argv[i + 1:]
    else:
        mine, enc_args = argv, []
    ap = argparse.ArgumentParser()
    ap.add_argument('outdir')
    ap.add_argument('timeout', type=int)
    ap.add_argument('--lrat', action='store_true')
    ap.add_argument('--cube', default='')
    ap.add_argument('--opts', default='', help='extra cadical options, comma separated')
    a = ap.parse_args(mine)
    out = pathlib.Path(a.outdir)
    out.mkdir(parents=True, exist_ok=True)
    cnf = out / 'f.cnf'
    ea = benc.parse_args(enc_args + ['-o', str(cnf)])
    t0 = time.time()
    e = benc.build_from_args(ea)
    cube = [int(x) for x in a.cube.split(',') if x.strip()]
    for l in cube:
        e.add([l], 'cube')
    e.dimacs(str(cnf))
    meta = e.meta()
    gen = time.time() - t0
    rec = solve(cnf, out, a.timeout, a.lrat, [o for o in a.opts.split(',') if o])
    rec['gen_seconds'] = gen
    rec['enc_args'] = enc_args
    rec['cube'] = cube
    rec['vars'], rec['clauses'] = e.nv, len(e.cls)
    rec['encoder_sha256'] = sha(HERE / 'benc.py')
    if rec['status'] == 'SAT':
        capmode, m = e.capmode, e.cap
        bc = (lambda c: c <= m) if capmode == 'atmost' else (lambda c: c == m) if capmode == 'exact' else None
        rep = check_sat(meta, rec.pop('model'), bc)
        rec['replay'] = rep
        if not rep['verified']:
            rec['status'] = 'SAT_REPLAY_FAILED'
    rec.pop('model', None)
    json.dump(rec, open(out / 'result.json', 'w'), indent=1)
    if rec['status'] in ('UNSAT_VERIFIED', 'UNSAT_UNCERTIFIED', 'UNKNOWN'):
        cnf.unlink(missing_ok=True)
    short = {k: rec.get(k) for k in ('status', 'seconds', 'vars', 'clauses', 'proof_bytes', 'chk1_out', 'chk2_out')}
    if 'replay' in rec:
        short['san'] = ' '.join(rec['replay']['san'])
        short['fen'] = rec['replay']['fen']
        short['captures'] = rec['replay']['captures']
    print(json.dumps(short))

if __name__ == '__main__':
    main()
