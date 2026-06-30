# Q2576: EulerSquarePair → PrimitiveCenteredFourSqAP helper layer

I could not inspect the user-local `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean` because this layer appears to be local/unpushed, so the final record field labels may need to be adjusted to the actual structure.  The helper lemmas below are written to avoid the most fragile `IsCoprime.add_mul_*` API names by using direct Bezout proofs.

Target namespace:

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair
```

The code assumes the local names from the prompt:

```lean
E.centerX, E.stepN, E.fm6, E.fm2, E.fp2, E.fp6
E.centerX_coprime_stepN
E.three_coprime_centerX
E.fm6_odd, E.fm2_odd, E.fp2_odd, E.fp6_odd
E.fm6_square, E.fm2_square, E.fp2_square, E.fp6_square
fm2_coprime_fp2 E
fm6_coprime_fp6 E
```

---

## 1. Robust local Bezout helpers

These helpers are useful because they avoid depending on the exact orientation of Mathlib’s transport lemmas.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12.EulerSquarePair

/-- Transport coprimality by replacing the left argument by `x + k*y`. -/
lemma isCoprime_add_mul_left_int {x y k : ℤ}
    (h : IsCoprime x y) :
    IsCoprime (x + k * y) y := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u, v - u * k, ?_⟩
  calc
    u * (x + k * y) + (v - u * k) * y = u * x + v * y := by ring
    _ = 1 := huv

/-- If `x` is coprime to `z`, then it is coprime to `x + z`. -/
lemma isCoprime_self_add_right_int {x z : ℤ}
    (h : IsCoprime x z) :
    IsCoprime x (x + z) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u - v, v, ?_⟩
  calc
    (u - v) * x + v * (x + z) = u * x + v * z := by ring
    _ = 1 := huv

/-- Bezout proof that coprimality with each factor gives coprimality with the product. -/
lemma isCoprime_mul_right_int {a b c : ℤ}
    (hab : IsCoprime a b) (hac : IsCoprime a c) :
    IsCoprime a (b * c) := by
  rcases hab with ⟨u, v, huv⟩
  rcases hac with ⟨r, s, hrs⟩
  refine ⟨u * r * a + u * s * c + v * r * b, v * s, ?_⟩
  calc
    (u * r * a + u * s * c + v * r * b) * a + (v * s) * (b * c)
        = (u * a + v * b) * (r * a + s * c) := by ring
    _ = 1 := by rw [huv, hrs]; ring

/-- An odd integer is Bezout-coprime to `2`. -/
lemma isCoprime_two_of_odd_int {m : ℤ} (hm : Odd m) :
    IsCoprime m (2 : ℤ) := by
  rcases hm with ⟨k, hk⟩
  refine ⟨1, -k, ?_⟩
  rw [hk]
  ring

lemma isCoprime_four_of_odd_int {m : ℤ} (hm : Odd m) :
    IsCoprime m (4 : ℤ) := by
  have h2 : IsCoprime m (2 : ℤ) := isCoprime_two_of_odd_int hm
  have h22 : IsCoprime m ((2 : ℤ) * 2) :=
    isCoprime_mul_right_int h2 h2
  simpa using h22

lemma isCoprime_eight_of_odd_int {m : ℤ} (hm : Odd m) :
    IsCoprime m (8 : ℤ) := by
  have h4 : IsCoprime m (4 : ℤ) := isCoprime_four_of_odd_int hm
  have h2 : IsCoprime m (2 : ℤ) := isCoprime_two_of_odd_int hm
  have h42 : IsCoprime m ((4 : ℤ) * 2) :=
    isCoprime_mul_right_int h4 h2
  simpa using h42
```

---

## 2. Shift-to-step coprimality lemmas

These are the common first step for all cross-factor coprimality proofs.

```lean
lemma fm6_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fm6 E.stepN := by
  have h := isCoprime_add_mul_left_int
    (x := E.centerX) (y := E.stepN) (k := (-6 : ℤ))
    E.centerX_coprime_stepN
  convert h using 1 <;> (simp [fm6]; ring)

lemma fm2_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fm2 E.stepN := by
  have h := isCoprime_add_mul_left_int
    (x := E.centerX) (y := E.stepN) (k := (-2 : ℤ))
    E.centerX_coprime_stepN
  convert h using 1 <;> (simp [fm2]; ring)

lemma fp2_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fp2 E.stepN := by
  have h := isCoprime_add_mul_left_int
    (x := E.centerX) (y := E.stepN) (k := (2 : ℤ))
    E.centerX_coprime_stepN
  convert h using 1 <;> (simp [fp2]; ring)

lemma fp6_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fp6 E.stepN := by
  have h := isCoprime_add_mul_left_int
    (x := E.centerX) (y := E.stepN) (k := (6 : ℤ))
    E.centerX_coprime_stepN
  convert h using 1 <;> (simp [fp6]; ring)
```

If the local file already has `fm2_coprime_stepN` etc. from Q2570, reuse those and omit this block.

---

## 3. Cross-factor coprimality lemmas

No `3`-stripping is needed for these four cross pairs, because the factor differences are only `4*N` or `8*N`:

```text
fm2 = fm6 + 4*N
fp2 = fm6 + 8*N
fp6 = fm2 + 8*N
fp6 = fp2 + 4*N
```

```lean
/-- `fm6` and `fm2` differ by `4*stepN`. -/
theorem fm6_coprime_fm2 (E : EulerSquarePair) :
    IsCoprime E.fm6 E.fm2 := by
  have hN : IsCoprime E.fm6 E.stepN := fm6_coprime_stepN E
  have h4 : IsCoprime E.fm6 (4 : ℤ) := isCoprime_four_of_odd_int E.fm6_odd
  have h4N : IsCoprime E.fm6 ((4 : ℤ) * E.stepN) :=
    isCoprime_mul_right_int h4 hN
  have h := isCoprime_self_add_right_int h4N
  convert h using 1 <;> (simp [fm6, fm2]; ring)

/-- `fm6` and `fp2` differ by `8*stepN`. -/
theorem fm6_coprime_fp2 (E : EulerSquarePair) :
    IsCoprime E.fm6 E.fp2 := by
  have hN : IsCoprime E.fm6 E.stepN := fm6_coprime_stepN E
  have h8 : IsCoprime E.fm6 (8 : ℤ) := isCoprime_eight_of_odd_int E.fm6_odd
  have h8N : IsCoprime E.fm6 ((8 : ℤ) * E.stepN) :=
    isCoprime_mul_right_int h8 hN
  have h := isCoprime_self_add_right_int h8N
  convert h using 1 <;> (simp [fm6, fp2]; ring)

/-- `fm2` and `fp6` differ by `8*stepN`. -/
theorem fm2_coprime_fp6 (E : EulerSquarePair) :
    IsCoprime E.fm2 E.fp6 := by
  have hN : IsCoprime E.fm2 E.stepN := fm2_coprime_stepN E
  have h8 : IsCoprime E.fm2 (8 : ℤ) := isCoprime_eight_of_odd_int E.fm2_odd
  have h8N : IsCoprime E.fm2 ((8 : ℤ) * E.stepN) :=
    isCoprime_mul_right_int h8 hN
  have h := isCoprime_self_add_right_int h8N
  convert h using 1 <;> (simp [fm2, fp6]; ring)

/-- `fp2` and `fp6` differ by `4*stepN`. -/
theorem fp2_coprime_fp6 (E : EulerSquarePair) :
    IsCoprime E.fp2 E.fp6 := by
  have hN : IsCoprime E.fp2 E.stepN := fp2_coprime_stepN E
  have h4 : IsCoprime E.fp2 (4 : ℤ) := isCoprime_four_of_odd_int E.fp2_odd
  have h4N : IsCoprime E.fp2 ((4 : ℤ) * E.stepN) :=
    isCoprime_mul_right_int h4 hN
  have h := isCoprime_self_add_right_int h4N
  convert h using 1 <;> (simp [fp2, fp6]; ring)
```

The already-proved endpoint/middle pair lemmas are still needed separately:

```lean
-- fm2_coprime_fp2 E : IsCoprime E.fm2 E.fp2
-- fm6_coprime_fp6 E : IsCoprime E.fm6 E.fp6
```

---

## 4. Root gcd from factor coprimality

The proof does **not** need a power-coprime API.  A Bezout certificate for `x,y`, after rewriting `x=p^2`, `y=q^2`, immediately gives a Bezout certificate for `p,q`:

```lean
/-- If two square values are coprime, then the corresponding roots are coprime. -/
lemma roots_isCoprime_of_sq_eq_of_isCoprime
    {p q x y : ℤ}
    (hp : p ^ 2 = x) (hq : q ^ 2 = y)
    (hxy : IsCoprime x y) :
    IsCoprime p q := by
  rcases hxy with ⟨a, b, hab⟩
  rw [← hp, ← hq] at hab
  refine ⟨a * p, b * q, ?_⟩
  calc
    (a * p) * p + (b * q) * q = a * (p ^ 2) + b * (q ^ 2) := by ring
    _ = 1 := hab

/-- GCD version used by `PrimitiveCenteredFourSqAP`. -/
lemma root_gcd_eq_one_of_sq_eq_of_isCoprime
    {p q x y : ℤ}
    (hp : p ^ 2 = x) (hq : q ^ 2 = y)
    (hxy : IsCoprime x y) :
    Int.gcd p q = 1 := by
  exact isCoprime_iff_gcd_eq_one.mp
    (roots_isCoprime_of_sq_eq_of_isCoprime hp hq hxy)
```

API pitfall: if the local file uses the `IsRelPrime` route, replace the final theorem body by the existing project idiom.  The statement above is the right reusable interface.  The usual current-Mathlib conversion is exactly:

```lean
isCoprime_iff_gcd_eq_one.mp h
```

---

## 5. Root parity/mod-2 from odd square value

This uses the fact that an odd product has odd factors.  The final API is `Int.odd_iff : Odd n ↔ n % 2 = 1`.

```lean
/-- If `p^2` is an odd integer, then `p % 2 = 1`. -/
lemma root_emod_two_eq_one_of_sq_eq_odd
    {p x : ℤ}
    (hp : p ^ 2 = x) (hx : Odd x) :
    p % 2 = 1 := by
  have hp2odd : Odd (p ^ 2) := by
    simpa [hp] using hx
  have hmulodd : Odd (p * p) := by
    simpa [pow_two] using hp2odd
  have hpodd : Odd p := hmulodd.of_mul_left
  exact Int.odd_iff.mp hpodd
```

Fallback if `Odd.of_mul_left` is not found in the pinned Mathlib:

```lean
  have hpodd : Odd p := by
    rcases hmulodd with ⟨k, hk⟩
    by_contra hpnot
    have hpeven : Even p := Int.not_odd_iff_even.mp hpnot
    rcases hpeven with ⟨t, ht⟩
    rw [ht] at hk
    have : ¬ Odd ((2 * t) * (2 * t)) := by
      exact not_odd_iff_even.mpr ⟨2 * t * t, by ring⟩
    exact this ⟨k, hk⟩
```

The first version is the preferred one.

---

## 6. Construction skeleton

The following is the intended proof shape.  The field labels in the record literal must be adjusted if `PrimitiveCenteredFourSqAP` uses different names.

```lean
theorem eulerSquarePairToPrimitiveCentered_constructive (E : EulerSquarePair) :
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D := by
  rcases E.fm6_square with ⟨p, hp⟩
  rcases E.fm2_square with ⟨q, hq⟩
  rcases E.fp2_square with ⟨r, hr⟩
  rcases E.fp6_square with ⟨s, hs⟩

  refine ⟨{
    X := E.centerX
    N := E.stepN
    p := p
    q := q
    r := r
    s := s

    hp := by
      -- target: p^2 = X - 6*N
      simpa [fm6] using hp
    hq := by
      -- target: q^2 = X - 2*N
      simpa [fm2] using hq
    hr := by
      -- target: r^2 = X + 2*N
      simpa [fp2] using hr
    hs := by
      -- target: s^2 = X + 6*N
      simpa [fp6] using hs

    hpq_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hp hq (fm6_coprime_fm2 E)
    hpr_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hp hr (fm6_coprime_fp2 E)
    hps_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hp hs (fm6_coprime_fp6 E)
    hqr_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hq hr (fm2_coprime_fp2 E)
    hqs_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hq hs (fm2_coprime_fp6 E)
    hrs_coprime :=
      root_gcd_eq_one_of_sq_eq_of_isCoprime hr hs (fp2_coprime_fp6 E)

    hp_odd := root_emod_two_eq_one_of_sq_eq_odd hp E.fm6_odd
    hq_odd := root_emod_two_eq_one_of_sq_eq_odd hq E.fm2_odd
    hr_odd := root_emod_two_eq_one_of_sq_eq_odd hr E.fp2_odd
    hs_odd := root_emod_two_eq_one_of_sq_eq_odd hs E.fp6_odd
  }, ?_⟩

  -- final target: constructed `T.N = E.A * E.D`
  simp [stepN]
```

If the structure fields are literally named as in the prompt rather than with proof-oriented labels, use this map:

```text
hp/hq/hr/hs             -> whatever fields state p^2/q^2/r^2/s^2
hpq_coprime             -> field for Int.gcd p q = 1
hpr_coprime             -> field for Int.gcd p r = 1
hps_coprime             -> field for Int.gcd p s = 1
hqr_coprime             -> field for Int.gcd q r = 1
hqs_coprime             -> field for Int.gcd q s = 1
hrs_coprime             -> field for Int.gcd r s = 1
hp_odd/hq_odd/hr_odd/hs_odd -> fields for p%2=q%2=r%2=s%2=1
```

The important orientation is:

```lean
p^2 = E.fm6
q^2 = E.fm2
r^2 = E.fp2
s^2 = E.fp6
```

so the six gcd calls pair exactly with:

```lean
fm6_coprime_fm2
fm6_coprime_fp2
fm6_coprime_fp6
fm2_coprime_fp2
fm2_coprime_fp6
fp2_coprime_fp6
```

end namespace when pasted into the file:

```lean
end MazurProof.RationalPointsN12.EulerSquarePair
```
