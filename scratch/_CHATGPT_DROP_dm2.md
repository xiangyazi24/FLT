# Q1476 (dm2): handling the `both_odd` issue in `quartic_plus`

## Bottom line

Do **not** try to prove `B₀` is odd at the `RationalPointsC20.lean` call site from `rat_denom_square` alone.  The denominator-square argument only proves

```text
u.den = B₀^2.
```

Equivalently, at each prime `p`, it proves that `v_p(u.den)` is even.  At `p = 2` this says

```text
v₂(u.den) = 2e
```

for some `e`; it does **not** say `e = 0`.  So `B₀` can still be even from the information provided by `rat_denom_square` alone.

The correct local architecture is to make `quartic_plus` handle parity internally:

1. Normalize `s` to `|s|` so `U < V` is available.
2. Split on `Even B`.
3. In the `¬ Even B` branch, get `Odd B` by `Int.not_even_iff_odd.mp`, and use the old `U,V` factors.
4. In the `Even B` branch, do **not** use `U,V` directly.  They are both divisible by `4`.  Instead use the primitive factors

```text
U₄ = U / 4,
V₄ = V / 4,
B₂ = B / 2.
```

Then the same product identity becomes

```text
U₄ * V₄ = 5 * B₂^4.
```

So the even branch is a separate 2-adic normalization branch.  This is better than pushing an oddness fact into the rational-point call site.

## Why call-site oddness is not safe

From the rational point equation you get, schematically,

```text
(w^2).den = (u^3 + u^2 - u).den = u.den^3.
```

Since `(w^2).den = w.den^2`, this gives

```text
u.den^3 = w.den^2.
```

Taking valuations gives

```text
3 * v_p(u.den) = 2 * v_p(w.den).
```

Hence `v_p(u.den)` is even.  For `p = 2`, this only gives `v₂(u.den) = 0, 2, 4, ...`.  It does **not** rule out `v₂(u.den) = 2`, which would make `B₀ = sqrt(u.den)` even.

So the statement

```lean
u.den = B₀ ^ 2
```

plus the curve equation proves square denominator, not odd square denominator.

## Lean skeleton: restructure `quartic_plus` by primitive factors

The following is the architecture I recommend.  It intentionally isolates the remaining arithmetic seams: the odd branch gcd, the even branch divisibility/gcd, and the final coprime factorization.

```lean
import Mathlib

namespace QuarticPlusParity

/-- Quartic-plus equation. -/
def Qeq (r B s : ℤ) : Prop :=
  s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- Classical factors. -/
def U (r B s : ℤ) : ℤ :=
  2 * r ^ 2 + B ^ 2 - 2 * s

def V (r B s : ℤ) : ℤ :=
  2 * r ^ 2 + B ^ 2 + 2 * s

lemma UV_product {r B s : ℤ} (hEq : Qeq r B s) :
    U r B s * V r B s = 5 * B ^ 4 := by
  unfold Qeq at hEq
  unfold U V
  calc
    (2 * r ^ 2 + B ^ 2 - 2 * s) * (2 * r ^ 2 + B ^ 2 + 2 * s)
        = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by ring
    _ = 5 * B ^ 4 := by
      rw [show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hEq]
      ring

/-- The primitive factor package used by both parity branches. -/
structure PrimitiveFactors (r B s : ℤ) : Prop where
  Bp : ℤ
  Up : ℤ
  Vp : ℤ
  hBp_pos : 0 < Bp
  hBp_le : Bp.natAbs ≤ B.natAbs
  hUp_pos : 0 < Up
  hVp_pos : 0 < Vp
  hUp_lt_Vp : Up < Vp
  hprod : Up * Vp = 5 * Bp ^ 4
  hcop : Int.gcd Up Vp = 1

/-- Odd branch: use the original factors.

Here `Odd B` makes `U,V` odd, and the usual gcd proof gives `gcd U V = 1`.
-/
lemma primitiveFactors_odd_B
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hs : 0 < s)
    (hBodd : Odd B)
    (hcop_rB : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    PrimitiveFactors r B s := by
  classical
  refine
    { Bp := B
      Up := U r B s
      Vp := V r B s
      hBp_pos := hB
      hBp_le := le_rfl
      hUp_pos := ?_
      hVp_pos := ?_
      hUp_lt_Vp := ?_
      hprod := UV_product hEq
      hcop := ?_ }
  · -- positivity of `U`; use product positivity and positivity of `V`.
    -- This is the same lemma as in the previous drop.
    sorry
  · unfold V
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero r (ne_of_gt hr)
    have hB2 : 0 < B ^ 2 := sq_pos_of_ne_zero B (ne_of_gt hB)
    nlinarith
  · unfold U V
    nlinarith
  · -- gcd seam for the odd branch.  The proof uses:
    -- `U,V` odd, common divisor divides `V-U = 4s` and `U+V = 2(2r^2+B^2)`,
    -- then coprimality of `r,B` rules out odd prime common divisors.
    sorry

/-- Even branch divisibility: if `B` is even, then `r` and `s` are odd, and `4 ∣ U,V`.

This is the place to do the 2-adic normalization.  It can be proved with `Even`/`Odd`
lemmas rather than explicit `% 2` arithmetic:

* `Even B` and `gcd r B = 1` imply `Odd r`.
* The equation then implies `Odd s`.
* For odd `r,s` and even `B`, both `2*r^2+B^2-2*s` and
  `2*r^2+B^2+2*s` are divisible by `4`.
-/
lemma even_B_four_dvd_UV
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hBeven : Even B)
    (hcop_rB : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    (4 : ℤ) ∣ U r B s ∧ (4 : ℤ) ∣ V r B s := by
  -- Suggested implementation details:
  --   have hrOdd : Odd r := ...       -- from `hcop_rB` and `hBeven`
  --   have hsOdd : Odd s := ...       -- from `hEq`, `hrOdd`, `hBeven`
  --   rcases hBeven with ⟨b, hb⟩
  --   rcases hrOdd with ⟨a, ha⟩
  --   rcases hsOdd with ⟨c, hc⟩
  --   constructor <;> refine ⟨_, ?_⟩ <;> unfold U V <;> rw [hb, ha, hc] <;> ring
  sorry

/-- Even branch product after dividing both factors by `4`.

If `B = 2*B₂`, `4 ∣ U`, and `4 ∣ V`, then

`(U/4)*(V/4) = 5*(B/2)^4`.
-/
lemma even_B_primitive_product
    {r B s : ℤ}
    (hEq : Qeq r B s)
    (hU4 : (4 : ℤ) ∣ U r B s)
    (hV4 : (4 : ℤ) ∣ V r B s)
    (hBeven : Even B) :
    (U r B s / 4) * (V r B s / 4) = 5 * (B / 2) ^ 4 := by
  rcases hU4 with ⟨U4, hU4⟩
  rcases hV4 with ⟨V4, hV4⟩
  rcases hBeven with ⟨B2, hB2⟩
  have hB2' : B = 2 * B2 := by
    rw [hB2, two_mul]
  have hUdiv : U r B s / 4 = U4 := by
    rw [hU4, Int.mul_ediv_cancel_left]
    norm_num
  have hVdiv : V r B s / 4 = V4 := by
    rw [hV4, Int.mul_ediv_cancel_left]
    norm_num
  have hBdiv : B / 2 = B2 := by
    rw [hB2', Int.mul_ediv_cancel_left]
    norm_num
  have hprod := UV_product hEq
  rw [hU4, hV4, hB2'] at hprod
  rw [hUdiv, hVdiv, hBdiv]
  nlinarith

/-- Even branch gcd seam after stripping the forced factor `4`.

This is the replacement for `both_odd`.  In the even case the raw `U,V` are not coprime,
but the primitive factors `U/4,V/4` should be coprime.
-/
lemma even_B_primitive_gcd
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hs : 0 < s)
    (hBeven : Even B)
    (hcop_rB : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    Int.gcd (U r B s / 4) (V r B s / 4) = 1 := by
  -- Same common-divisor proof as odd branch, but applied after removing the forced 2-adic factor.
  -- Common divisor of `U/4,V/4` divides `s` and `r^2 + B^2/2`; use `gcd r B = 1`.
  sorry

/-- Even branch package. -/
lemma primitiveFactors_even_B
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hs : 0 < s)
    (hBeven : Even B)
    (hcop_rB : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    PrimitiveFactors r B s := by
  classical
  obtain ⟨hU4, hV4⟩ := even_B_four_dvd_UV hr hB hBeven hcop_rB hEq
  refine
    { Bp := B / 2
      Up := U r B s / 4
      Vp := V r B s / 4
      hBp_pos := ?_
      hBp_le := ?_
      hUp_pos := ?_
      hVp_pos := ?_
      hUp_lt_Vp := ?_
      hprod := even_B_primitive_product hEq hU4 hV4 hBeven
      hcop := even_B_primitive_gcd hr hB hs hBeven hcop_rB hEq }
  · rcases hBeven with ⟨B2, hB2⟩
    have hB2' : B = 2 * B2 := by rw [hB2, two_mul]
    rw [hB2', Int.mul_ediv_cancel_left]
    · nlinarith
    · norm_num
  · -- `0 < B` and `Even B` imply `0 < B/2 ≤ B` in natAbs.
    sorry
  · -- positivity of `U/4` from positivity of `U` and divisibility by positive `4`.
    sorry
  · -- positivity of `V/4`.
    sorry
  · -- follows from `U < V` and division by positive `4` after divisibility.
    sorry

/-- Parity-independent primitive factor extraction.

This is the theorem that should replace the old “both odd” entry point. -/
theorem primitiveFactors_of_quarticPlus
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hs : 0 < s)
    (hcop_rB : Int.gcd r B = 1)
    (hEq : Qeq r B s) :
    PrimitiveFactors r B s := by
  by_cases hBeven : Even B
  · exact primitiveFactors_even_B hr hB hs hBeven hcop_rB hEq
  · have hBodd : Odd B := Int.not_even_iff_odd.mp hBeven
    exact primitiveFactors_odd_B hr hB hs hBodd hcop_rB hEq

end QuarticPlusParity
```

## How this changes the descent proof

Instead of making the descent theorem take an `Odd B` hypothesis, change the first half to return primitive factors:

```lean
obtain PF := primitiveFactors_of_quarticPlus hr hB hs hcop hEq
```

Then run the coprime factorization lemma on

```lean
PF.Up * PF.Vp = 5 * PF.Bp ^ 4
PF.hcop : Int.gcd PF.Up PF.Vp = 1
```

This removes the need for a global `both_odd` hypothesis.

For the strong induction on `B.natAbs`, the even branch is actually friendly: `PF.Bp = B/2`, so `PF.Bp.natAbs < B.natAbs`.  That gives a direct smaller-denominator object once the second-half descent constructs a new solution using `PF.Bp`.

## If you prefer an even-`B` contradiction lemma

You can also keep the old odd-branch descent and prove:

```lean
lemma quarticPlus_even_B_absurd
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hBeven : Even B)
    (hcop : Int.gcd r B = 1)
    (hEq : Qeq r B s) : False := by
  -- either a 2-adic descent or a primitive-factor descent specialized to contradiction
  sorry
```

Then the main proof is:

```lean
by_cases hBeven : Even B
· exact False.elim (quarticPlus_even_B_absurd hr hB hBeven hcop hEq)
· have hBodd : Odd B := Int.not_even_iff_odd.mp hBeven
  -- old both-odd proof
```

This is clean, but it hides the real work in `quarticPlus_even_B_absurd`.  The primitive-factor architecture above is more reusable and closer to the mathematics.

## Recommendation

Do not try to force `B₀` odd in `RationalPointsC20.lean`.  Make `quartic_plus` parity-robust:

* odd `B`: use `U,V`;
* even `B`: use `U/4,V/4,B/2`.

That removes the fragile call-site dependency and turns the `both_odd` issue into a local 2-adic normalization lemma inside the descent file.
