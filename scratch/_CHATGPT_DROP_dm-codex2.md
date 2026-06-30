# Q2559 Euler pair factor-square extraction layer

This note is for `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`, after the local helper layer already has:

```lean
@[simp] def centerX (E : EulerSquarePair) : ℤ := E.B * E.C
@[simp] def stepN   (E : EulerSquarePair) : ℤ := E.A * E.D
@[simp] def fm6     (E : EulerSquarePair) : ℤ := E.centerX - 6 * E.stepN
@[simp] def fm2     (E : EulerSquarePair) : ℤ := E.centerX - 2 * E.stepN
@[simp] def fp2     (E : EulerSquarePair) : ℤ := E.centerX + 2 * E.stepN
@[simp] def fp6     (E : EulerSquarePair) : ℤ := E.centerX + 6 * E.stepN
```

and checked positivity/parity helpers:

```lean
stepN_pos, stepN_even, centerX_pos,
B_odd, C_odd, centerX_odd,
fp2_pos, fp6_pos, fm2_pos_of_fm6_pos
```

The next reconstruction layer has four independent pieces:

1. prove `fm6_pos`, hence `fm2_pos`;
2. prove the two factor coprimality lemmas;
3. use a square-product extraction lemma for positive coprime integer factors;
4. package roots for `fm2`, `fp2`, `fm6`, `fp6`.

The adversarial point is important: the outer coprimality

```lean
IsCoprime E.fm6 E.fp6
```

is **not** a consequence of only `centerX_coprime_stepN`, parity, and positivity.  One also needs the derived lemma

```lean
three_coprime_centerX (E) : IsCoprime (3 : ℤ) E.centerX
```

or an equivalent statement.  Without it, the model example `X = 15`, `N = 2` has `gcd(X,N)=1`, `X` odd, `N` even, `X - 6N = 3`, `X + 6N = 27`, so the outer pair is not coprime.  This example is not asserted to come from an `EulerSquarePair`; it shows exactly why the `3`-lemma cannot be skipped.

## 1. Product identities in factor form

Keep the checked algebra identities separate from the factor form consumed by the extraction lemma.

```lean
namespace EulerSquarePair

-- If your checked theorem already has this exact statement, keep that theorem name.
theorem middle_factor_product_square (E : EulerSquarePair) :
    E.fm2 * E.fp2 = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 := by
  -- From the checked identity
  --   (B*C)^2 - (2*(A*D))^2 = (D^2 + 8*A^2)^2
  -- plus `(x-y)*(x+y) = x^2-y^2`.
  -- Expected proof:
  --   dsimp [fm2, fp2, centerX, stepN]
  --   calc ... := by ring
  --        _ = ... := eulerPair_middle_product_square E
  -- Do not duplicate if already present locally.
  -- fill with existing checked theorem and `ring`.
  omega -- placeholder line to delete; this block is a target shape, not pasteable as-is.

-- If your checked theorem already has this exact statement, keep that theorem name.
theorem outer_factor_product_square (E : EulerSquarePair) :
    E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
  -- Same pattern from the checked outer identity.
  -- fill with existing checked theorem and `ring`.
  omega -- placeholder line to delete; this block is a target shape, not pasteable as-is.

end EulerSquarePair
```

The two theorem statements above are the stable API to use below.  Do not paste the `omega` placeholders; they are only there to keep the target shape visually explicit in this note.  If you want pasteable code, write the `calc` proof against your actual checked theorem names.

## 2. Positivity of `fm6`

The extra lemma needed for `fm6_pos` is:

```lean
theorem Dsq_sub_8Asq_ne_zero (E : EulerSquarePair) :
    E.D ^ 2 - 8 * E.A ^ 2 ≠ 0
```

It follows by parity: `D^2` is odd and `8*A^2` is even, hence the difference is odd and cannot be zero.  This uses only `E.hDodd`; `E.hAeven` is not needed.

A robust proof shape, assuming the earlier local `odd_sq_of_odd_int` helper from Q2555 exists:

```lean
namespace EulerSquarePair

private theorem even_eight_mul_sq (a : ℤ) : Even (8 * a ^ 2) := by
  refine ⟨4 * a ^ 2, ?_⟩
  ring

private theorem odd_sub_even_ne_zero {a b : ℤ}
    (ha : Odd a) (hb : Even b) : a - b ≠ 0 := by
  intro hzero
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  rw [hu, hv] at hzero
  omega

theorem Dsq_sub_8Asq_ne_zero (E : EulerSquarePair) :
    E.D ^ 2 - 8 * E.A ^ 2 ≠ 0 := by
  exact odd_sub_even_ne_zero (odd_sq_of_odd_int E.hDodd) (even_eight_mul_sq E.A)

end EulerSquarePair
```

Then `fm6_pos` comes from the outer product identity plus `fp6_pos`:

```lean
namespace EulerSquarePair

theorem fm6_pos (E : EulerSquarePair) : 0 < E.fm6 := by
  have hprod : E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
    outer_factor_product_square E
  have hsqpos : 0 < (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
    exact sq_pos_of_ne_zero (Dsq_sub_8Asq_ne_zero E)
  have hmulpos : 0 < E.fm6 * E.fp6 := by
    rw [hprod]
    exact hsqpos
  have hfp6 : 0 < E.fp6 := fp6_pos E
  by_contra hnot
  have hfm6_nonpos : E.fm6 ≤ 0 := le_of_not_gt hnot
  have hfp6_nonneg : 0 ≤ E.fp6 := le_of_lt hfp6
  have hmul_nonpos : E.fm6 * E.fp6 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hfm6_nonpos hfp6_nonneg
  linarith

theorem fm2_pos (E : EulerSquarePair) : 0 < E.fm2 :=
  fm2_pos_of_fm6_pos E (fm6_pos E)

end EulerSquarePair
```

API names to check if needed:

```lean
#check sq_pos_of_ne_zero
#check mul_nonpos_of_nonpos_of_nonneg
#check le_of_not_gt
```

If `sq_pos_of_ne_zero` is not available for `ℤ` in your snapshot, replace it with a tiny local lemma:

```lean
-- target only:
-- theorem int_sq_pos_of_ne_zero {z : ℤ} (hz : z ≠ 0) : 0 < z ^ 2
```

and prove it by cases `z < 0`, `z = 0`, `0 < z`, or by `nlinarith [sq_nonneg z]` after excluding equality.

## 3. Oddness of the four factors

You need these for stripping powers of `2` from common divisors.

```lean
namespace EulerSquarePair

-- These should compile if `Odd.add`, `Odd.sub`, and an even-multiple lemma are available.
-- Otherwise expand witnesses manually.
theorem fm2_odd (E : EulerSquarePair) : Odd E.fm2 := by
  dsimp [fm2]
  exact (centerX_odd E).sub (Even.mul_left (2 : ℤ) (stepN_even E))

theorem fp2_odd (E : EulerSquarePair) : Odd E.fp2 := by
  dsimp [fp2]
  exact (centerX_odd E).add (Even.mul_left (2 : ℤ) (stepN_even E))

theorem fm6_odd (E : EulerSquarePair) : Odd E.fm6 := by
  dsimp [fm6]
  exact (centerX_odd E).sub (Even.mul_left (6 : ℤ) (stepN_even E))

theorem fp6_odd (E : EulerSquarePair) : Odd E.fp6 := by
  dsimp [fp6]
  exact (centerX_odd E).add (Even.mul_left (6 : ℤ) (stepN_even E))

end EulerSquarePair
```

If `Even.mul_left` has the opposite orientation, use explicit witnesses from `stepN_even` instead:

```lean
-- Given `stepN = 2*k`, prove `2*stepN`, `6*stepN` even by witnesses.
```

## 4. Divisor-stripping helpers for `IsCoprime`

The factor coprimality proofs are clean if you isolate these helpers.  They are small and reusable.

```lean
namespace EulerSquarePair

-- API-sensitive target.  Search/check first:
#check IsCoprime.dvd_of_dvd_mul_left
#check IsCoprime.dvd_of_dvd_mul_right
#check Odd.isCoprime_two
#check Odd.coprime_two

-- Target statement, not fake code:
-- theorem isCoprime_two_of_dvd_odd {d m : ℤ}
--     (hm : Odd m) (hdm : d ∣ m) : IsCoprime d (2 : ℤ)
-- Proof route: `Odd m` gives `IsCoprime m 2`; then use divisor monotonicity
-- of `IsCoprime` on the left because `d ∣ m`.

-- Target statement, not fake code:
-- theorem dvd_of_dvd_two_mul_of_coprime_two {d x : ℤ}
--     (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 2 * x) : d ∣ x
-- Proof route: use `IsCoprime.dvd_of_dvd_mul_left/right`, depending on API orientation.

-- Target statement, not fake code:
-- theorem dvd_of_dvd_four_mul_of_coprime_two {d x : ℤ}
--     (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 4 * x) : d ∣ x
-- Proof route: derive `IsCoprime d (4 : ℤ)` from `hd2.pow_right 2`, then strip `4`.

-- Target statement, not fake code:
-- theorem dvd_of_dvd_twelve_mul_of_coprime_two_three {d x : ℤ}
--     (hd2 : IsCoprime d (2 : ℤ))
--     (hd3 : IsCoprime d (3 : ℤ))
--     (h : d ∣ 12 * x) : d ∣ x
-- Proof route: combine `hd2` and `hd3` to get `IsCoprime d (12 : ℤ)`;
-- then strip `12`.

end EulerSquarePair
```

The exact method names to search are:

```lean
#check IsCoprime.of_dvd_left
#check IsCoprime.of_dvd_right
#check IsCoprime.mul_right
#check IsCoprime.pow_right
#check IsCoprime.dvd_of_dvd_mul_left
#check IsCoprime.dvd_of_dvd_mul_right
```

If the method names differ, prove the helpers directly from the divisor criterion for `IsCoprime`.

## 5. Middle factor coprimality

Dependency:

```text
centerX_coprime_stepN
fm2_odd
common divisor algebra:
  d | fm2, d | fp2
  ⇒ d | fm2 + fp2 = 2*centerX
  ⇒ d | fp2 - fm2 = 4*stepN
strip powers of 2 using oddness
  ⇒ d | centerX, d | stepN
centerX_coprime_stepN
  ⇒ IsUnit d
```

Target theorem:

```lean
namespace EulerSquarePair

theorem fm2_coprime_fp2 (E : EulerSquarePair) : IsCoprime E.fm2 E.fp2 := by
  intro d hdfm hdfp
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd (fm2_odd E) hdfm

  have hsum : d ∣ E.fm2 + E.fp2 := dvd_add hdfm hdfp
  have h2X : d ∣ 2 * E.centerX := by
    convert hsum using 1
    dsimp [fm2, fp2]
    ring
  have hdX : d ∣ E.centerX :=
    dvd_of_dvd_two_mul_of_coprime_two hd2 h2X

  have hdiff : d ∣ E.fp2 - E.fm2 := dvd_sub hdfp hdfm
  have h4N : d ∣ 4 * E.stepN := by
    convert hdiff using 1
    dsimp [fm2, fp2]
    ring
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_four_mul_of_coprime_two hd2 h4N

  exact (centerX_coprime_stepN E) hdX hdN

end EulerSquarePair
```

This proof is structurally exact.  It compiles once the four small stripping helpers from §4 are provided with the local Mathlib method names.

## 6. The required `3`-lemma for the outer pair

You need:

```lean
theorem three_coprime_centerX (E : EulerSquarePair) :
    IsCoprime (3 : ℤ) E.centerX
```

This is not an extra structure field.  It is derived from `E.hB`, `E.hC`, and `E.hADcop` by a modulo-3 square argument.

Suggested theorem DAG:

```lean
namespace EulerSquarePair

-- Target statement, proof via ZMod 3 or prime divisibility.
-- theorem three_coprime_B (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.B
-- If `3 | B`, then modulo 3 the equation
--   B^2 = 16*A^2 + D^2
-- gives `0 = A^2 + D^2` in `ZMod 3`.
-- Over `ZMod 3`, squares are `0` or `1`, so this forces `A = 0` and `D = 0`
-- modulo 3, contradicting `E.hADcop`.

-- Target statement, same proof with `C^2 = 4*A^2 + D^2`.
-- theorem three_coprime_C (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.C

-- Then combine:
-- theorem three_coprime_centerX (E : EulerSquarePair) :
--     IsCoprime (3 : ℤ) E.centerX := by
--   dsimp [centerX]
--   exact (three_coprime_B E).mul_right (three_coprime_C E)

end EulerSquarePair
```

API names to check for the modulo-3 proof:

```lean
#check ZMod
#check Int.cast_zmod_eq_zero_iff_dvd
#check IsCoprime
#check IsCoprime.symm
```

Alternatively prove `¬ (3 : ℤ) ∣ E.B` and use a prime/coprime API.  Search:

```lean
#check Prime.coprime_iff_not_dvd
#check Int.prime_three
#check Nat.prime_three
```

Again, the warning is adversarial: without this lemma or equivalent, the outer coprimality claim is false in the abstract `X,N` algebra.

## 7. Outer factor coprimality

Dependency:

```text
centerX_coprime_stepN
three_coprime_centerX
fm6_odd
common divisor algebra:
  d | fm6, d | fp6
  ⇒ d | fm6 + fp6 = 2*centerX
  ⇒ d | fp6 - fm6 = 12*stepN
strip 2 from the first divisor relation
  ⇒ d | centerX
from d | centerX and IsCoprime 3 centerX
  ⇒ IsCoprime d 3
from fm6 odd and d | fm6
  ⇒ IsCoprime d 2
strip 12 from the second divisor relation
  ⇒ d | stepN
centerX_coprime_stepN
  ⇒ IsUnit d
```

Target theorem:

```lean
namespace EulerSquarePair

theorem fm6_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fm6 E.fp6 := by
  intro d hdfm hdfp
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd (fm6_odd E) hdfm

  have hsum : d ∣ E.fm6 + E.fp6 := dvd_add hdfm hdfp
  have h2X : d ∣ 2 * E.centerX := by
    convert hsum using 1
    dsimp [fm6, fp6]
    ring
  have hdX : d ∣ E.centerX :=
    dvd_of_dvd_two_mul_of_coprime_two hd2 h2X

  have hd3 : IsCoprime d (3 : ℤ) := by
    -- From `three_coprime_centerX E : IsCoprime 3 centerX`
    -- and `hdX : d ∣ centerX`.
    -- Search/check: `IsCoprime.of_dvd_right`, `IsCoprime.of_dvd_left`.
    -- Exact orientation depends on local API; no fake code here.
    -- mathematically: any common divisor of d and 3 also divides centerX and 3.
    exact isCoprime_three_of_dvd_centerX E hdX

  have hdiff : d ∣ E.fp6 - E.fm6 := dvd_sub hdfp hdfm
  have h12N : d ∣ 12 * E.stepN := by
    convert hdiff using 1
    dsimp [fm6, fp6]
    ring
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_twelve_mul_of_coprime_two_three hd2 hd3 h12N

  exact (centerX_coprime_stepN E) hdX hdN

end EulerSquarePair
```

The only non-expanded helper in that theorem is:

```lean
-- target only:
-- theorem isCoprime_three_of_dvd_centerX
--     (E : EulerSquarePair) {d : ℤ} (hdX : d ∣ E.centerX) :
--     IsCoprime d (3 : ℤ)
```

It follows by divisor monotonicity from `three_coprime_centerX E`, after applying symmetry if needed.

## 8. Square-product extraction lemma

Do **not** infer individual squares from `a*b = z^2` alone.  The needed lemma is positive + coprime.

Search/check the Mathlib API first:

```lean
#check Int.sq_of_isCoprime
#check Nat.sq_of_coprime
#check Nat.Coprime
#check IsSquare
```

I could not confirm a current top-level name from the connector, so the robust local interface should be this wrapper:

```lean
-- Target theorem.  Implement once, preferably as a local wrapper over Mathlib's
-- `Int.sq_of_isCoprime` if `#check Int.sq_of_isCoprime` succeeds.
theorem exists_pos_sq_factors_of_isCoprime_mul_eq_sq
    {a b z : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hab : IsCoprime a b)
    (hmul : a * b = z ^ 2) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ r ^ 2 = a ∧ s ^ 2 = b
```

Implementation route:

```text
1. Use Mathlib's coprime square-product theorem to get `∃ r0, r0^2 = a`
   and `∃ s0, s0^2 = b`.
2. Normalize signs by `r = |r0|`, `s = |s0|`.
3. Positivity follows because `a,b > 0`, so the roots are nonzero.
4. `(|r0|)^2 = r0^2` by `sq_abs` or a small `ring_nf`/case proof.
```

If no integer theorem is available, convert to naturals using positivity:

```text
an := a.toNat, bn := b.toNat, zn := z.natAbs
an * bn = zn^2
Nat.Coprime an bn
```

then use the natural-number coprime square-factor theorem, and cast back to `ℤ`.

Optional odd-enhanced wrapper for AP roots:

```lean
-- Target theorem, after `odd_of_sq_odd_int` is already local.
theorem exists_pos_odd_sq_factors_of_isCoprime_mul_eq_sq
    {a b z : ℤ}
    (ha : 0 < a)
    (hb : 0 < b)
    (haodd : Odd a)
    (hbodd : Odd b)
    (hab : IsCoprime a b)
    (hmul : a * b = z ^ 2) :
    ∃ r s : ℤ,
      0 < r ∧ 0 < s ∧ Odd r ∧ Odd s ∧
      r ^ 2 = a ∧ s ^ 2 = b
```

This simply calls the positive wrapper and proves root oddness from `r^2 = a`, `s^2 = b`, and oddness of `a,b`.

## 9. Root extraction statements

Once the preceding lemmas are in place, the middle extraction is direct:

```lean
namespace EulerSquarePair

theorem middle_roots (E : EulerSquarePair) :
    ∃ q r : ℤ,
      0 < q ∧ 0 < r ∧ Odd q ∧ Odd r ∧
      q ^ 2 = E.fm2 ∧ r ^ 2 = E.fp2 := by
  exact exists_pos_odd_sq_factors_of_isCoprime_mul_eq_sq
    (fm2_pos E)
    (fp2_pos E)
    (fm2_odd E)
    (fp2_odd E)
    (fm2_coprime_fp2 E)
    (middle_factor_product_square E)

end EulerSquarePair
```

The outer extraction is the same, using `fm6_pos`, `fp6_pos`, and the `3`-aware coprimality theorem:

```lean
namespace EulerSquarePair

theorem outer_roots (E : EulerSquarePair) :
    ∃ p s : ℤ,
      0 < p ∧ 0 < s ∧ Odd p ∧ Odd s ∧
      p ^ 2 = E.fm6 ∧ s ^ 2 = E.fp6 := by
  exact exists_pos_odd_sq_factors_of_isCoprime_mul_eq_sq
    (fm6_pos E)
    (fp6_pos E)
    (fm6_odd E)
    (fp6_odd E)
    (fm6_coprime_fp6 E)
    (outer_factor_product_square E)

end EulerSquarePair
```

Then combine all four roots into a local data package:

```lean
structure EulerPairRootData (E : EulerSquarePair) where
  p q r s : ℤ
  hp_pos : 0 < p
  hq_pos : 0 < q
  hr_pos : 0 < r
  hs_pos : 0 < s
  hp_odd : Odd p
  hq_odd : Odd q
  hr_odd : Odd r
  hs_odd : Odd s
  hp_sq : p ^ 2 = E.fm6
  hq_sq : q ^ 2 = E.fm2
  hr_sq : r ^ 2 = E.fp2
  hs_sq : s ^ 2 = E.fp6

namespace EulerSquarePair

theorem rootData (E : EulerSquarePair) : EulerPairRootData E := by
  obtain ⟨q, r, hqpos, hrpos, hqodd, hrodd, hqsq, hrsq⟩ := middle_roots E
  obtain ⟨p, s, hppos, hspos, hpodd, hsodd, hpsq, hssq⟩ := outer_roots E
  exact
    { p := p, q := q, r := r, s := s
      hp_pos := hppos, hq_pos := hqpos, hr_pos := hrpos, hs_pos := hspos
      hp_odd := hpodd, hq_odd := hqodd, hr_odd := hrodd, hs_odd := hsodd
      hp_sq := hpsq, hq_sq := hqsq, hr_sq := hrsq, hs_sq := hssq }

end EulerSquarePair
```

This data is enough for the square equations of `PrimitiveCenteredFourSqAP`.  The pairwise gcd fields among `p,q,r,s` still need the six cross-coprimality facts among `fm6`, `fm2`, `fp2`, `fp6`, plus the standard lemma that coprime square values imply coprime roots.

## 10. Minimal dependency DAG

```text
outer_factor_product_square
Dsq_sub_8Asq_ne_zero
fp6_pos
  ⇒ fm6_pos
fm6_pos
fm2_pos_of_fm6_pos
  ⇒ fm2_pos

centerX_coprime_stepN
fm2_odd / fp2_odd
strip-2 divisor helpers
  ⇒ fm2_coprime_fp2

three_coprime_centerX
centerX_coprime_stepN
fm6_odd / fp6_odd
strip-2 and strip-12 divisor helpers
  ⇒ fm6_coprime_fp6

middle_factor_product_square
fm2_pos, fp2_pos, fm2_coprime_fp2
square-product extraction
  ⇒ middle_roots

outer_factor_product_square
fm6_pos, fp6_pos, fm6_coprime_fp6
square-product extraction
  ⇒ outer_roots
```

The genuine new arithmetic subfrontiers are therefore:

```lean
centerX_coprime_stepN        -- from Q2557 layer
three_coprime_centerX        -- needed only for the outer pair
exists_pos_sq_factors_of_isCoprime_mul_eq_sq
```

Everything else is local algebra, parity, or divisor bookkeeping.
