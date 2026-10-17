#!/usr/bin/env python3
"""Regenerate the columns Parts / max / times of the dense-window tables from the Lean modules
shipped in lean/, and re-verify each cover-capacity certificate with the independent Rust checker v1.

Usage (from the bundle root):  python3 code/dense/check_rows.py [V1_BINARY]
Reads  paper/dense-window/rows.tex, rows_ext.tex, lean/LRSpectrumFull/Delta2*.lean.
Writes a table to stdout; exit status 1 if any row disagrees or v1 rejects.
Thin glue: no large data structures.
"""
import re, subprocess, sys, tempfile, os
ROOT = os.getcwd()
V1 = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'build/dense/v1')
L = os.path.join(ROOT, 'lean/LRSpectrumFull')

def bracket(s, i):
    """s[i] is '[': return index just after the matching ']'."""
    d = 1
    j = i + 1
    while True:
        c = s[j]
        if c in '[{': d += 1
        elif c in ']}':
            d -= 1
            if d == 0: return j + 1
        j += 1

def cert_from_lean(m, mod):
    txt = open(f'{L}/Delta2{mod}.lean').read()
    if re.search(r'def UL : List', txt):                      # split style
        t = int(re.search(r'\(t := (\d+)\)', txt).group(1)); N = int(re.search(r'\(N := (\d+)\)', txt).group(1))
        UL = re.search(r'def UL : List \(List ℕ\) := (.*)', txt).group(1)
        parts = [list(map(int, p.split(','))) for p in re.findall(r'\[([\d,]+)\]', UL)]
        caps = [int(x) for x in re.search(r'def CL : List ℕ := \[(.*?)\]', txt).group(1).split(',')]
        return t, N, parts, caps
    k = re.search(r'theorem dense_floor_m%d(?:_split)? ' % m, txt).start()
    body = txt[k:]
    end = body.find('\n\n')
    body = body[:end]
    t = int(re.search(r'\(t := (\d+)\)', body).group(1)); N = int(re.search(r'\(N := (\d+)\)', body).group(1))
    lists = []
    for mm in re.finditer(r'!\[', body):
        lists.append(body[mm.start():bracket(body, mm.start() + 1)])
    # the last two lists are the parts (sets) and the capacities
    pj, cj = lists[-2], lists[-1]
    parts = [list(map(int, re.findall(r'\d+', s))) for s in re.findall(r'\{([\d,]*)\}', pj)]
    caps = [int(x) for x in re.findall(r'\d+', cj)]
    return t, N, parts, caps

rows = []
for f in ('paper/dense-window/rows.tex', 'paper/dense-window/rows_ext.tex'):
    for ln in open(os.path.join(ROOT, f)):
        c = [x.strip() for x in ln.rstrip('\n').rstrip('\\').split('&')]
        if len(c) < 7: continue
        mod = re.search(r'\\texttt\{([A-Za-z0-9]+)\}', c[6]).group(1)
        rows.append((int(c[0]), int(c[2]), int(c[3]), int(c[4]), mod))
bad = 0
print('m\tmodule\tparts\tmax\ttimes\tsum_cap\tv1\tstatus')
for m, tp, mx, tn, mod in sorted(rows):
    t, N, parts, caps = cert_from_lean(m, mod)
    assert len(parts) == t == len(caps)
    ok = (t == tp and max(len(p) for p in parts) == mx and N == tn and sum(caps) == m - 1)
    with tempfile.NamedTemporaryFile('w', suffix='.sol', delete=False) as fh:
        for p, c in zip(parts, caps): fh.write(f'{c} ' + ' '.join(map(str, p)) + '\n')
        name = fh.name
    out = subprocess.run([V1, 'check', str(m), name, 'list'], capture_output=True, text=True).stdout.strip()
    os.unlink(name)
    acc = 'ACCEPT' in out
    st = 'OK' if (ok and acc) else 'FAIL'
    bad += st != 'OK'
    print(f'{m}\t{mod}\t{t}\t{max(len(p) for p in parts)}\t{N}\t{sum(caps)}\t{"ACCEPT" if acc else "REJECT"}\t{st}')
# composite lists (the statement of Section "table" of the paper)
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
comp = lambda a, b: [m for m in range(a, b + 1) if not isprime(2 * m + 1)]
have = sorted(r[0] for r in rows)
frac = [4, 7, 12, 13]
low_ok = sorted([m for m in have if m <= 62] + frac) == comp(2, 62)
exc = [m for m in comp(63, 126) if m not in have]
exc_ok = exc == [94, 97, 103, 109, 115, 122]
print(f'composite m in [2,62]: {len(comp(2,62))}, covered by rows+Table1: {low_ok}; composite in [63,126]: {len(comp(63,126))}, exceptions {exc}: {exc_ok}')
bad += (not low_ok) + (not exc_ok)
print(f'rows {len(rows)}, failures {bad}')
sys.exit(1 if bad else 0)
