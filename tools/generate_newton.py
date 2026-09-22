"""Generate small Newton-factorization witnesses over F_2.

This script is NOT a proof checker or a trusted dependency.  Each resulting
identity is proved by Lean's proof-producing ring and norm_num tactics.
Run from the project root to regenerate HoffmanChromatic/NewtonData.lean.
"""
from pathlib import Path


def mul(a, b):
    ans = 0
    while b:
        if b & 1:
            ans ^= a
        a <<= 1
        b >>= 1
    return ans


def power(a, n):
    ans = 1
    for _ in range(n):
        ans = mul(ans, a)
    return ans


def divide(a, b):
    ans = 0
    while a and a.bit_length() >= b.bit_length():
        d = a.bit_length() - b.bit_length()
        ans ^= 1 << d
        a ^= b << d
    assert a == 0, "non-exact Newton division"
    return ans


def expr(a):
    return " + ".join(
        "1" if d == 0 else "z" if d == 1 else f"z^{d}"
        for d in range(a.bit_length()) if (a >> d) & 1
    ) or "0"


e = [0, 1, 3, 4, 8, 9, 11]
U = [[0] * 7 for _ in range(7)]
W = [[0] * 7 for _ in range(7)]
W[0][0] = 1
for b in range(1, 7):
    for j in range(b + 1):
        W[j][b] = (W[j][b-1] << j) ^ (W[j-1][b-1] if j else 0)
for i in range(7):
    f = 1
    for j in range(7):
        U[i][j] = divide(f, power(3, e[j]))
        f = mul(f, (1 << i) ^ (1 << j))

header = '''import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Explicit Newton witnesses for the two coordinate alphabets.

`newtonU z i j` is the quotient of the Newton evaluation
  product_{r < j} (z^i - z^r)
by `(z + 1)^e_j` in characteristic two. `newtonW` expresses the
monomials in the monic Newton basis. The small tables are witnesses;
the theorems below check every polynomial identity in Lean's kernel.
They hold for a formal indeterminate, not merely for numerical samples.
-/

namespace HoffmanChromatic

open scoped BigOperators
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

instance f2SeriesCharP : CharP (PowerSeries (ZMod 2)) 2 :=
  ⟨fun n => by
    rw [← map_natCast (PowerSeries.C (ZMod 2)) n, ← map_zero (PowerSeries.C (ZMod 2)),
      PowerSeries.C_injective.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod 2) 2 n⟩

theorem reduceSeriesNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : PowerSeries (ZMod 2)) = ((n % 2 : ℕ) : PowerSeries (ZMod 2)) :=
  CharP.cast_eq_mod _ 2 n

def newtonExponent : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 8
  | 5 => 9
  | 6 => 11
  | _ => 0

'''
chunks = [header]
for name, data in [("newtonU", U), ("newtonW", W)]:
    chunks.append(f"noncomputable def {name} (z : PowerSeries (ZMod 2)) : ℕ → ℕ → PowerSeries (ZMod 2)\n")
    for i, row in enumerate(data):
        for j, p in enumerate(row):
            if p:
                chunks.append(f"  | {i}, {j} => {expr(p)}\n")
    chunks.append("  | _, _ => 0\n\n")
for q in (6, 7):
    for i in range(q):
        for b in range(q):
            rhs = "0"
            for j in reversed(range(q)):
                rhs = f"(z+1)^{e[j]} * (({expr(U[i][j])}) * ({expr(W[j][b])})) + ({rhs})"
            chunks.append(f'''private theorem newton_entry_{q}_{i}_{b} (z : PowerSeries (ZMod 2)) :
    z^({i} * {b}) = ∑ j : Fin {q},
      (z + 1)^newtonExponent j.val * (newtonU z {i} j.val * newtonW z j.val {b}) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change z^{i*b} = {rhs}
  ring_nf
''')
            if i*b:
                chunks.append("  simp only [reduceSeriesNat]\n  norm_num\n")
            chunks.append("\n")
    chunks.append(f'''set_option maxHeartbeats 4000000 in
theorem newton_factor_{q} (z : PowerSeries (ZMod 2)) (i b : Fin {q}) :
    z^(i.val * b.val) = ∑ j : Fin {q},
      (z + 1)^newtonExponent j.val * (newtonU z i.val j.val * newtonW z j.val b.val) := by
  fin_cases i <;> fin_cases b
''')
    for i in range(q):
        for b in range(q):
            chunks.append(f"  · exact newton_entry_{q}_{i}_{b} z\n")
    chunks.append("\n")
chunks.append("end HoffmanChromatic\n")
Path("HoffmanChromatic/NewtonData.lean").write_text("".join(chunks))
