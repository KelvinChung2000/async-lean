#!/usr/bin/env python3
"""The fast explicit check split across files, checked by parallel Lean processes.

usage: bench/xfile.py NET K JOBS      e.g. bench/xfile.py "handshakes 7" 8 4

Writes to bench/xfile/: `Cert.lean` (the certificate and literals, as definitions), `Part<i>.lean`
(the kernel check of the i-th key range), `Glue.lean` (`(NET).Correct` from the parts), then
checks Cert, the parts with JOBS processes in parallel, and Glue, and prints the times.
"""
import os, resource, subprocess, sys, time

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = os.path.join(root, 'bench', 'parts.py')
ns = {}
exec(open(src).read().split("\ndef run")[0], ns)
HEADER = ns['HEADER']

net, K, jobs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
d = os.path.join(root, 'bench', 'xfile')
bd = os.path.join(d, 'build', 'BX')
os.makedirs(bd, exist_ok=True)

cert = HEADER.replace('open AsyncLean\n', 'open AsyncLean Lean Elab Command Meta\n') + f'''
def net : PNet := {net}

elab "fast_setup " k:num : command => liftTermElabM do
  let Nv ← Tactic.evalAs PNet (mkConst `net)
  let .ok (w, c) := Nv.mkFastCert true true true 10000000 | throwError "no certificate"
  let K := k.getNat
  let B := 2 ^ w
  let add (n : Name) (ty v : Expr) : MetaM Unit := addDecl (.defnDecl {{ name := n,
    levelParams := [], type := ty, value := v, hints := .opaque, safety := .safe }})
  let natT := mkConst ``Nat
  add `cert (mkConst ``Fast.Cert) (FastExpr.certE c)
  add `tbl (FastExpr.listT (mkConst ``PNet.FEntry))
    (FastExpr.listE (mkConst ``PNet.FEntry) ((Nv.ftable w).map FastExpr.fentryE))
  add `wv natT (mkRawNatLit w)
  add `Bv natT (mkRawNatLit B)
  add `fmv natT (mkRawNatLit (B - 1))
  add `kv natT (mkRawNatLit Nv.imask)
  add `s0v natT (mkRawNatLit (PNet.encW w Nv.init))
  let keys := (c.1.toList.map (·.1)).toArray.qsort (· < ·)
  let bs := ((List.range K).filterMap fun i =>
    if i == 0 then none else keys[i * keys.size / K]?).filter (· != 0) |>.eraseDups
  add `bounds (FastExpr.listT natT) (FastExpr.listE natT ((0 :: bs ++ [0]).map mkRawNatLit))
  logInfo m!"states {{keys.size}} parts {{bs.length + 1}}"

fast_setup {K}

noncomputable def Fv : ℕ → List (ℕ × ℕ × Bool) := PNet.fsucc fmv Bv tbl
'''
open(os.path.join(d, 'Cert.lean'), 'w').write(cert)

def lean(name):
    env = dict(os.environ)
    return ['lake', 'env', 'sh', '-c',
            f'LEAN_PATH=$LEAN_PATH:{d}/build lean -o {bd}/{name}.olean {d}/{name}.lean']

def timed(cmds, jobs):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    procs, outs, i = [], [], 0
    while i < len(cmds) or procs:
        while i < len(cmds) and len(procs) < jobs:
            procs.append(subprocess.Popen(cmds[i], cwd=root, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT, text=True))
            i += 1
        p = procs.pop(0)
        out = p.communicate()[0]
        if p.returncode != 0 or 'error' in out:
            print(out[:2000]); sys.exit(1)
        outs.append(out)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return time.time() - t0, (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime), outs

w, c, outs = timed([lean('Cert')], 1)
info = [l for l in outs[0].splitlines() if 'states' in l]
nparts = int(info[0].split('parts')[1])
print(f'{net}: {info[0].strip()}')
print(f'  Cert   wall {w:7.1f} s  cpu {c:7.1f} s')

for i in range(nparts):
    open(os.path.join(d, f'Part{i}.lean'), 'w').write(f'''import BX.Cert
open AsyncLean
theorem part{i} : Fast.checkPart Fv kv true true cert (bounds.getD {i} 0) (bounds.getD {i + 1} 0) =
    true := by decide +kernel
''')

def glue(i, j):
    if j <= i + 1: return f'part{i}'
    m = (i + j) // 2
    return f'(Fast.checkPart_split (bounds.getD {m} 0) rfl {glue(i, m)} {glue(m, j)})'

imports = '\n'.join(f'import BX.Part{i}' for i in range(nparts))
open(os.path.join(d, 'Glue.lean'), 'w').write(f'''{imports}
open AsyncLean
theorem pre : net.checkFastPre wv Bv fmv tbl kv true s0v = true := by decide +kernel
theorem head : Fast.checkHead Fv net.trans.length true s0v cert = true := by decide +kernel
theorem all : Fast.checkPart Fv kv true true cert 0 0 = true := {glue(0, nparts)}
theorem t : net.Correct := PNet.correct_of_checkFast (PNet.checkFast_of_parts pre head all)
''')

w, c, _ = timed([lean(f'Part{i}') for i in range(nparts)], jobs)
print(f'  Parts  wall {w:7.1f} s  cpu {c:7.1f} s  ({nparts} parts, {jobs} jobs)')
w, c, _ = timed([lean('Glue')], 1)
print(f'  Glue   wall {w:7.1f} s  cpu {c:7.1f} s')
