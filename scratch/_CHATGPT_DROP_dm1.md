# Q30 (dm1): Keystone avenue (c) — division-polynomial coprimality

## Executive answer

The adjacent-Somos avenue is useful, but it does **not** prove the stated theorem as written.  The missing point is local invertibility: the propagation step from two adjacent vanishing `preΨ` values needs

```lean
(W.Ψ₃.eval x) ≠ 0
```

not merely the polynomial-level hypothesis

```lean
W.Ψ₃ ≠ 0.
```

Also, the displayed theorem has no nonsingularity/`IsElliptic` hypothesis.  With only `h4`, `hψ_ne`, and polynomial-level `hc3`, the no-common-root statement is not a valid target.  The singular cusp over `ℚ`, with

```text
b2 = b4 = b6 = b8 = 0,
```

has

```text
s  = 4*X^3,
Ψ₃ = 3*X^4,
preΨ₄ = 2*X^6.
```

For `n = 3`, using `preΨ₂ = 1`,

```text
ΨSq 3 = Ψ₃^2 = 9*X^8,
Φ 3   = X*Ψ₃^2 - preΨ₄*preΨ₂*Ψ₂Sq
      = 9*X^9 - 8*X^9
      = X^9.
```

Thus both evaluate to zero at `X = 0`.  This curve satisfies `bRel` and `4 ≠ 0`, and `Ψ₃` is a nonzero polynomial.  Therefore the desired theorem needs at least a nonsingularity hypothesis, or an equivalent hypothesis ruling out common roots of the basic torsion factors.

The non-circular route I recommend is:

1. Add or derive a nonsingularity hypothesis, preferably `hEll : W.IsElliptic` or `W.discr ≠ 0`.
2. Prove finite base-resultant lemmas, especially:
   ```lean
   W.Ψ₂Sq.eval x = 0 → W.Ψ₃.eval x ≠ 0
   W.Ψ₃.eval x = 0 → W.Ψ₂Sq.eval x ≠ 0 ∧ W.preΨ 4 |>.eval x ≠ 0
   ```
3. Use adjacent-Somos to prove no adjacent vanishing on the open stratum `Ψ₃.eval x ≠ 0`.
4. Use the `Ψ₃.eval x = 0` stratum as the rank-three base case.  This is a small rank-of-apparition argument, not a one-line propagation from adjacent Somos.
5. Then prove the `n = 2*m+1` specialization by expanding the definitions of `Φ` and `ΨSq` and reducing to “no adjacent preΨ vanishing” plus the 2-torsion lemma.

The rest of this note gives the exact recurrence rearrangement, the 2-torsion handling, and a Lean skeleton for the specialization.

---

## 1. Exact adjacent-Somos propagation

Let

```lean
a i := (W.preΨ i).eval x
sx  := W.Ψ₂Sq.eval x
c3x := W.Ψ₃.eval x
```

The evaluated adjacent-Somos relation is

```text
a(r-2) * a(r+2)
  - (if Even r then 1 else sx^2) * (a(r-1) * a(r+1))
  + c3x * a(r)^2 = 0.
```

If `a r = 0` and `a (r+1) = 0`, then applying this at center `r-1` gives

```text
c3x * a(r-1)^2 = 0.
```

So, if `c3x ≠ 0`, then `a(r-1) = 0`.  The adjacent zero pair moves left:

```text
(a r = 0 ∧ a(r+1) = 0) ⟹ (a(r-1) = 0 ∧ a r = 0).
```

Similarly, applying the relation at center `r+2` gives

```text
c3x * a(r+2)^2 = 0,
```

so the pair also moves right:

```text
(a r = 0 ∧ a(r+1) = 0) ⟹ (a(r+1) = 0 ∧ a(r+2) = 0).
```

This part is correct and formalizable.  The crucial caveat is that it proves no adjacent vanishing only on the open set `Ψ₃.eval x ≠ 0`.

A Lean skeleton for the open-stratum propagation is:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

private abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k :=
  (W.preΨ i).eval x

private abbrev sx (W : WeierstrassCurve k) (x : k) : k :=
  W.Ψ₂Sq.eval x

private abbrev c3x (W : WeierstrassCurve k) (x : k) : k :=
  W.Ψ₃.eval x

private lemma eval_preΨ_adjacent_somos
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0) (r : ℤ) :
    pe W x (r - 2) * pe W x (r + 2)
      - (if Even r then 1 else (sx W x)^2) * (pe W x (r - 1) * pe W x (r + 1))
      + c3x W x * (pe W x r)^2 = 0 := by
  -- Uses the already-proved polynomial identity:
  --   preΨ_adjacent_somos W h4 r
  -- and evaluates at x.
  simpa [pe, sx, c3x, map_mul, map_add, map_sub, pow_two]
    using congrArg (fun p : k[X] => p.eval x) (preΨ_adjacent_somos W h4 r)

private lemma preΨ_prev_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r - 1) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r - 1)
  have hsquare : c3x W x * (pe W x (r - 1))^2 = 0 := by
    -- h is the relation at center r-1:
    -- a(r-3)*a(r+1) - eps*a(r-2)*a(r) + c3*a(r-1)^2 = 0.
    -- The first two products vanish by hr1 and hr.
    simpa [pe, sx, c3x, hr, hr1, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm, pow_two] using h
  have hsq : (pe W x (r - 1))^2 = 0 := by
    exact (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact sq_eq_zero_iff.mp hsq

private lemma preΨ_next_zero_of_adjacent_zero
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    {r : ℤ} (hc3x : c3x W x ≠ 0)
    (hr : pe W x r = 0) (hr1 : pe W x (r + 1) = 0) :
    pe W x (r + 2) = 0 := by
  have h := eval_preΨ_adjacent_somos W x h4 (r + 2)
  have hsquare : c3x W x * (pe W x (r + 2))^2 = 0 := by
    -- h is the relation at center r+2:
    -- a(r)*a(r+4) - eps*a(r+1)*a(r+3) + c3*a(r+2)^2 = 0.
    -- The first two products vanish by hr and hr1.
    simpa [pe, sx, c3x, hr, hr1, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm, pow_two] using h
  have hsq : (pe W x (r + 2))^2 = 0 := by
    exact (mul_eq_zero.mp hsquare).resolve_left hc3x
  exact sq_eq_zero_iff.mp hsq

private lemma no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
    (W : WeierstrassCurve k) (x : k) (h4 : (4 : k) ≠ 0)
    (hc3x : c3x W x ≠ 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  intro hz
  -- Move the adjacent zero pair until it contains index 1, then use preΨ_one.
  -- For r ≥ 1: repeatedly apply preΨ_prev_zero_of_adjacent_zero.
  -- For r ≤ 0: repeatedly apply preΨ_next_zero_of_adjacent_zero.
  -- The integer bookkeeping is routine with omega/Int.toNat.
  -- The terminal contradiction is:
  --   have h1 : pe W x 1 = 0 := ...
  --   simpa [pe, preΨ_one] using h1
  by_cases hr : 1 ≤ r
  · -- Downward induction on Int.toNat (r - 1).
    -- Skeleton:
    --   let N : ℕ := Int.toNat (r - 1)
    --   induction N generalizing r with
    --   | zero => omega gives r = 1, then hz.left contradicts preΨ_one
    --   | succ N ih =>
    --       have hprev := preΨ_prev_zero_of_adjacent_zero W x h4 hc3x hz.left hz.right
    --       exact ih (r := r - 1) ... ⟨hprev, hz.left⟩
    omega
  · -- Upward induction on Int.toNat (-r).
    -- Terminal pair is (0,1), whose right component contradicts preΨ_one.
    -- Same shape as the previous branch, using preΨ_next_zero_of_adjacent_zero.
    omega

end

end WeierstrassCurve
```

The final two `omega` placeholders are the only omitted bookkeeping in this local lemma; no algebra remains there.  If desired, they can be replaced by an explicit `Int.le_induction` or `Nat` induction on `Int.toNat (r - 1)` / `Int.toNat (-r)`.

---

## 2. The 2-torsion case `Ψ₂Sq.eval x = 0`

For the odd specialization `n = 2*m + 1`, the denominator is

```text
ΨSq n = preΨ n ^ 2
```

because `n` is odd.  Thus a common root forces `a n = 0`.  If additionally `sx = 0`, the `Φ` equation is automatic from the displayed definition unless we prove separately that odd-indexed `preΨ` values do not vanish at a nonsingular 2-torsion `x`.

The clean lemma is:

```lean
private lemma preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero
    (W : WeierstrassCurve k) (x : k)
    (hEll : W.IsElliptic) (h4 : (4 : k) ≠ 0)
    (hs : sx W x = 0) {n : ℤ} (hnodd : ¬ Even n) :
    pe W x n ≠ 0 := by
  -- Use hEll to prove c3x W x ≠ 0 at a root of Ψ₂Sq.
  -- Then reduce to positive odd indices using preΨ_neg.
  -- For positive odd indices, do strong induction.
  -- Bases:
  --   preΨ 1 = 1
  --   preΨ 3 = Ψ₃, nonzero by c3x_ne
  -- Step uses preΨ_odd:
  --   if Even t:
  --     a(2*t+1) = a(t+2)*a(t)^3*sx^2 - a(t-1)*a(t+1)^3
  --              = - a(t-1)*a(t+1)^3
  --   if ¬ Even t:
  --     a(2*t+1) = a(t+2)*a(t)^3 - a(t-1)*a(t+1)^3*sx^2
  --              = a(t+2)*a(t)^3
  -- since sx = 0.
  -- The smaller odd indices are handled by the induction hypothesis.
  sorry
```

The required nonsingularity sublemma is finite and independent of keystone induction:

```lean
private lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_of_isElliptic
    (W : WeierstrassCurve k) (x : k)
    (hEll : W.IsElliptic) (hs : W.Ψ₂Sq.eval x = 0) :
    W.Ψ₃.eval x ≠ 0 := by
  -- Conceptual proof:
  --   resultant(Ψ₂Sq, Ψ₃) = -discr(W)^2
  -- after using bRel.
  -- A common root would force the resultant to vanish, hence discr(W)=0,
  -- contradicting hEll.
  -- This can be made a finite polynomial certificate; no keystone theorem is used.
  sorry
```

For reference, with the expanded constants in the prompt,

```text
resultant_X(s, c3) = -Δ^2   modulo bRel,
```

where

```text
Δ = -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6.
```

Equivalently,

```text
resultant_X(s,c3) + Δ^2
  = -4*bRel*(3*b2^2*b4*b8 + b2^2*b6^2 - 20*b2*b4^2*b6
      - 8*b2*b6*b8 + 16*b4^4 - 28*b4^2*b8
      + 81*b4*b6^2 + 16*b8^2).
```

That is the finite certificate behind the 2-torsion separation lemma.

---

## 3. The odd specialization skeleton

Once the two independent inputs below are available,

```lean
hNoAdj : ∀ r : ℤ, ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0)
hOdd2 : ∀ {n : ℤ}, ¬ Even n → sx W x = 0 → pe W x n ≠ 0
```

then the `n = 2*m+1` no-common-root proof is short and non-circular:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

private abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k :=
  (W.preΨ i).eval x

private abbrev sx (W : WeierstrassCurve k) (x : k) : k :=
  W.Ψ₂Sq.eval x

private lemma odd_index_two_mul_add_one (m : ℤ) : ¬ Even (2*m + 1 : ℤ) := by
  omega

private lemma ΨSq_eval_odd
    (W : WeierstrassCurve k) (x : k) {n : ℤ} (hn : ¬ Even n) :
    (W.ΨSq n).eval x = (pe W x n)^2 := by
  -- ΨSq n = preΨ n^2 * if Even n then Ψ₂Sq else 1.
  simp [pe, WeierstrassCurve.ΨSq, hn, pow_two]

private lemma Φ_eval_odd
    (W : WeierstrassCurve k) (x : k) {n : ℤ} (hn : ¬ Even n) :
    (W.Φ n).eval x =
      x * (W.ΨSq n).eval x
        - pe W x (n + 1) * pe W x (n - 1) * sx W x := by
  -- Φ n = X*ΨSq n - preΨ(n+1)*preΨ(n-1)*(if Even n then 1 else Ψ₂Sq).
  simp [pe, sx, WeierstrassCurve.Φ, hn, mul_assoc, mul_left_comm, mul_comm]

private theorem Φ_ΨSq_no_common_eval_zero_odd_from_no_adjacent
    (W : WeierstrassCurve k) (x : k) (m : ℤ)
    (hNoAdj : ∀ r : ℤ, ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0))
    (hOdd2 : ∀ {n : ℤ}, ¬ Even n → sx W x = 0 → pe W x n ≠ 0) :
    (W.ΨSq (2*m + 1)).eval x = 0 → (W.Φ (2*m + 1)).eval x ≠ 0 := by
  intro hΨ hΦ
  let n : ℤ := 2*m + 1
  have hn : ¬ Even n := by
    dsimp [n]
    omega
  have hΨ' : (pe W x n)^2 = 0 := by
    simpa [n] using (show (W.ΨSq n).eval x = 0 from hΨ) ▸ (by
      simpa using ΨSq_eval_odd W x hn)
  have hpn : pe W x n = 0 := sq_eq_zero_iff.mp hΨ'
  by_cases hs : sx W x = 0
  · exact (hOdd2 hn hs hpn).elim
  · have hΦeq := Φ_eval_odd W x hn
    have hprod_s : pe W x (n + 1) * pe W x (n - 1) * sx W x = 0 := by
      -- Substitute hΨ and hΦ into Φ_eval_odd.
      -- The `x * ΨSq` term is zero because hΨ = 0.
      have := hΦeq
      -- In a live Lean file, this is just a `linear_combination` or `nlinarith`
      -- after `simp [hΦ, hΨ, n, mul_assoc]`.
      sorry
    have hprod : pe W x (n + 1) * pe W x (n - 1) = 0 := by
      exact (mul_eq_zero.mp hprod_s).resolve_right hs
    rcases mul_eq_zero.mp hprod with hn1 | hnm1
    · -- Pair (n,n+1) vanishes.
      exact hNoAdj n ⟨hpn, hn1⟩
    · -- Pair (n-1,n) vanishes.
      have hz : pe W x (n - 1) = 0 ∧ pe W x ((n - 1) + 1) = 0 := by
        constructor
        · exact hnm1
        · simpa using hpn
      exact hNoAdj (n - 1) hz

end

end WeierstrassCurve
```

The proof above intentionally factors out the true hard lemma: `hNoAdj`.  The adjacent-Somos propagation proves `hNoAdj` on the stratum `Ψ₃.eval x ≠ 0`.  The remaining stratum `Ψ₃.eval x = 0` is a rank-three base case and cannot be closed by the same propagation step because the propagation coefficient has become zero.

---

## 4. The `Ψ₃.eval x = 0` stratum

This is the exact place where the proposed proof otherwise gets stuck.  At a point with `c3x = 0`, adjacent Somos becomes

```text
a(r-2) * a(r+2)
  = (if Even r then 1 else sx^2) * (a(r-1) * a(r+1)).
```

If `sx ≠ 0`, all displayed parity coefficients are nonzero, but the recurrence is multiplicative and does not force a neighboring square to vanish.  Hence the “two adjacent zeros propagate to `preΨ 1`” proof is unavailable on this stratum.

The independent finite base facts needed here are:

```lean
private lemma Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
    (W : WeierstrassCurve k) (x : k)
    (hEll : W.IsElliptic) (hc3 : W.Ψ₃.eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  -- resultant(Ψ₂Sq, Ψ₃) = -Δ^2 modulo bRel
  sorry

private lemma preΨ_four_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
    (W : WeierstrassCurve k) (x : k)
    (hEll : W.IsElliptic) (hc3 : W.Ψ₃.eval x = 0) :
    (W.preΨ 4).eval x ≠ 0 := by
  -- resultant(Ψ₃, preΨ₄) = Δ^4 modulo bRel
  sorry
```

With those, one proves the rank-three pattern at such an `x`:

```lean
private lemma preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) (hEll : W.IsElliptic) (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0) (n : ℤ) :
    pe W x n = 0 ↔ (3 : ℤ) ∣ n := by
  -- Use:
  --   preΨ_one,
  --   preΨ_two/preΨ₂ = 1,
  --   preΨ_three = Ψ₃,
  --   preΨ_four nonzero,
  --   preΨ_odd and preΨ_even recurrences.
  -- The induction is on |n| and splits n modulo 3.
  -- This is the usual rank-of-apparition argument specialized to rank 3.
  sorry
```

Then no adjacent vanishing on the `Ψ₃` stratum follows immediately, since two adjacent integers cannot both be divisible by `3`:

```lean
private lemma no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) (hEll : W.IsElliptic) (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0) (r : ℤ) :
    ¬ (pe W x r = 0 ∧ pe W x (r + 1) = 0) := by
  intro hz
  have hr3 : (3 : ℤ) ∣ r :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero W x hEll h4 hc3 r).mp hz.left
  have hr13 : (3 : ℤ) ∣ r + 1 :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero W x hEll h4 hc3 (r + 1)).mp hz.right
  omega
```

Combining `Ψ₃.eval x ≠ 0` and `Ψ₃.eval x = 0` gives the desired global `hNoAdj` under `IsElliptic`.

---

## 5. Resultant route

A resultant proof is conceptually cleaner:

```lean
theorem isCoprime_Φ_ΨSq_of_isElliptic
    (W : WeierstrassCurve k) (hEll : W.IsElliptic) (n : ℤ) :
    IsCoprime (W.Φ n) (W.ΨSq n) := by
  -- Show resultant(Φ n, ΨSq n) is a nonzero scalar:
  --   resultant(Φ n, ΨSq n) = unit(n) * W.discr ^ e(n)
  -- Then use hEll.
  sorry
```

Then the no-common-root theorem is one line:

```lean
private theorem no_common_eval_zero_of_isCoprime
    {f g : k[X]} (hcop : IsCoprime f g) (x : k) :
    ¬ (f.eval x = 0 ∧ g.eval x = 0) := by
  rcases hcop with ⟨a, b, hab⟩
  intro h
  have := congrArg (fun p : k[X] => p.eval x) hab
  simpa [h.1, h.2] using this
```

But for variable `n`, the resultant formula is a substantial theorem.  Mathlib has `Polynomial.resultant`, but it does not provide the division-polynomial resultant formula.  For a fixed finite certificate, a CAS-produced Bezout identity is practical; for all `n`, the Ward/rank-of-apparition proof above is the more realistic Lean route.

---

## 6. What the hypotheses buy

* `h4 : (4:k) ≠ 0` is genuinely useful.  It gives characteristic not `2`, keeps the `Ψ₂Sq` square-factor decomposition meaningful, and is required by the already-proved adjacent-Somos and invariant lemmas in this development.

* `hψ_ne : ∀ j:ℤ, j ≠ 0 → W.ψ j ≠ 0` is a polynomial-level nonzero hypothesis used to establish the recurrence/invariant library.  It is **not** an evaluation nonvanishing statement at the particular `x`, so it cannot by itself rule out common roots.

* `hc3 : W.Ψ₃ ≠ 0` is also polynomial-level.  It is useful for polynomial saturation/cancellation arguments, but the adjacent-zero propagation needs the stronger local assumption `(W.Ψ₃.eval x) ≠ 0`, or a separate proof of the `Ψ₃.eval x = 0` rank-three stratum.

* The 2-torsion branch really needs characteristic not `2` plus nonsingularity.  Algebraically, this is the statement that `Ψ₂Sq` and `Ψ₃` have no common root on an elliptic curve; equivalently, a 2-torsion root is simple.

## Bottom line

The proposed adjacent propagation is correct only after strengthening `hc3` to the local condition `Ψ₃.eval x ≠ 0`.  It gives an excellent open-stratum lemma.  To obtain the non-circular theorem needed by keystone, add an independent nonsingularity hypothesis and prove the two finite resultant/base lemmas for the `Ψ₂Sq` and `Ψ₃` strata.  Without that extra input, the theorem as stated is false on singular curves, and the Lean proof should not try to close it from `preΨ_adjacent_somos` alone.
