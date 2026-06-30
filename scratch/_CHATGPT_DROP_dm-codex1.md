# Q2570: next EulerSquarePair coprimality layer

Target namespace:

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair
```

I could not inspect the user-local `N12FourSquaresAP.lean` because this layer appears to be local/unpushed, so the code below assumes the names in the prompt are exactly available by dot notation:

```lean
E.centerX_coprime_stepN
E.fm2_odd
E.fp2_odd
E.fm6_odd
E.fp6_odd
E.three_coprime_centerX
```

The main API point: `IsCoprime` is a Bezout predicate, but current Mathlib has the needed transport lemmas:

```lean
h.symm
h.mul_right
h.add_mul_right_left
h.mul_add_right_right
IsCoprime.dvd_of_dvd_mul_left
IsCoprime.dvd_of_dvd_mul_right
```

The orientation pitfall is that

```lean
h.dvd_of_dvd_mul_left : IsCoprime x y -> x ∣ y*z -> x ∣ z
h.dvd_of_dvd_mul_right : IsCoprime x z -> x ∣ y*z -> x ∣ y
```

so “left/right” names refer to which multiplicand is stripped, not to which conclusion is returned.

---

## 1. Reusable `Int` coprime/stripping lemmas

Paste this near the current elementary number-theory helper layer.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12.EulerSquarePair

/-- An odd integer is Bezout-coprime to `2`. -/
lemma isCoprime_two_of_odd {m : ℤ} (hm : Odd m) :
    IsCoprime m (2 : ℤ) := by
  rcases hm with ⟨k, hk⟩
  change ∃ u v : ℤ, u * m + v * (2 : ℤ) = 1
  refine ⟨1, -k, ?_⟩
  rw [hk]
  ring

/-- Any integer divisor of an odd integer is odd. -/
lemma odd_of_dvd_odd {d m : ℤ} (hm : Odd m) (hdm : d ∣ m) :
    Odd d := by
  rcases hdm with ⟨k, rfl⟩
  exact hm.of_mul_left

/-- Any integer divisor of an odd integer is coprime to `2`. -/
lemma isCoprime_two_of_dvd_odd {d m : ℤ} (hm : Odd m) (hdm : d ∣ m) :
    IsCoprime d (2 : ℤ) :=
  isCoprime_two_of_odd (odd_of_dvd_odd hm hdm)

/-- An odd integer is coprime to `4`. -/
lemma isCoprime_four_of_odd {m : ℤ} (hm : Odd m) :
    IsCoprime m (4 : ℤ) := by
  have h2 : IsCoprime m (2 : ℤ) := isCoprime_two_of_odd hm
  have h22 : IsCoprime m ((2 : ℤ) * 2) := h2.mul_right h2
  simpa using h22

/-- Strip a factor `2` from the right of a divisibility hypothesis. -/
lemma dvd_of_dvd_two_mul_of_isCoprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ (2 : ℤ) * x) :
    d ∣ x :=
  hd2.dvd_of_dvd_mul_left h

/-- Strip a factor `4` from the right of a divisibility hypothesis. -/
lemma dvd_of_dvd_four_mul_of_isCoprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ (4 : ℤ) * x) :
    d ∣ x := by
  have hd4 : IsCoprime d (4 : ℤ) := by
    have h22 : IsCoprime d ((2 : ℤ) * 2) := hd2.mul_right hd2
    simpa using h22
  exact hd4.dvd_of_dvd_mul_left h

/-- Strip a factor `12 = 4*3` from the right of a divisibility hypothesis. -/
lemma dvd_of_dvd_twelve_mul_of_isCoprime_two_three {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ))
    (hd3 : IsCoprime d (3 : ℤ))
    (h : d ∣ (12 : ℤ) * x) :
    d ∣ x := by
  have hd4 : IsCoprime d (4 : ℤ) := by
    have h22 : IsCoprime d ((2 : ℤ) * 2) := hd2.mul_right hd2
    simpa using h22
  have hd12 : IsCoprime d (12 : ℤ) := by
    have h43 : IsCoprime d ((4 : ℤ) * 3) := hd4.mul_right hd3
    simpa using h43
  exact hd12.dvd_of_dvd_mul_left h
```

If `hm.of_mul_left` is not available in the exact pinned Mathlib, replace only `odd_of_dvd_odd` with the local parity theorem already used in the primitive-root layer.  The rest of the layer does not depend on any special parity API.

---

## 2. Coprimality of the middle pair

This proof avoids a custom “common divisor” theorem.  It uses:

1. `fm2 = centerX - 2*stepN`, hence `fm2` is coprime to `stepN` by adding a multiple of `stepN` to `centerX`.
2. `fm2` is odd, hence coprime to `4`.
3. Therefore `fm2` is coprime to `4*stepN`.
4. `fp2 = fm2 + 4*stepN`, hence `fm2` is coprime to `fp2`.

```lean
/-- `fm2` is coprime to the step parameter. -/
lemma fm2_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fm2 E.stepN := by
  have h := E.centerX_coprime_stepN.add_mul_right_left (z := (-2 : ℤ))
  convert h using 1 <;> (simp [fm2]; ring)

/-- The two middle factors are coprime. -/
theorem fm2_coprime_fp2 (E : EulerSquarePair) :
    IsCoprime E.fm2 E.fp2 := by
  have hN : IsCoprime E.fm2 E.stepN := fm2_coprime_stepN E
  have h4 : IsCoprime E.fm2 (4 : ℤ) := isCoprime_four_of_odd E.fm2_odd
  have h4N : IsCoprime E.fm2 ((4 : ℤ) * E.stepN) := h4.mul_right hN
  have h := h4N.mul_add_right_right (z := (1 : ℤ))
  convert h using 1 <;> (simp [fm2, fp2]; ring)
```

This is stronger/cleaner than proving arbitrary-divisor stripping inside the final theorem, but it is exactly the same math: a common divisor of `fm2` and `fp2` divides `4*stepN`, and the oddness of `fm2` strips the `4`.

---

## 3. Coprimality of the outer pair

The outer case is the same, except the difference is `12*stepN`, and one must also remove the possible factor `3`.  The existing theorem

```lean
E.three_coprime_centerX : IsCoprime (3 : ℤ) E.centerX
```

is used after symmetry and adding the multiple `-2*stepN*3`:

```lean
E.fm6 = E.centerX + ((-2 : ℤ) * E.stepN) * 3.
```

```lean
/-- `fm6` is coprime to the step parameter. -/
lemma fm6_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.fm6 E.stepN := by
  have h := E.centerX_coprime_stepN.add_mul_right_left (z := (-6 : ℤ))
  convert h using 1 <;> (simp [fm6]; ring)

/-- `fm6` is coprime to `3`, using `centerX` coprime to `3`. -/
lemma fm6_coprime_three (E : EulerSquarePair) :
    IsCoprime E.fm6 (3 : ℤ) := by
  have hcx3 : IsCoprime E.centerX (3 : ℤ) := E.three_coprime_centerX.symm
  have h := hcx3.add_mul_right_left (z := (-2 : ℤ) * E.stepN)
  convert h using 1 <;> (simp [fm6]; ring)

/-- An odd integer coprime to `3` is coprime to `12`. -/
lemma isCoprime_twelve_of_odd_of_isCoprime_three {m : ℤ}
    (hm : Odd m) (h3 : IsCoprime m (3 : ℤ)) :
    IsCoprime m (12 : ℤ) := by
  have h4 : IsCoprime m (4 : ℤ) := isCoprime_four_of_odd hm
  have h43 : IsCoprime m ((4 : ℤ) * 3) := h4.mul_right h3
  simpa using h43

/-- The two outer factors are coprime. -/
theorem fm6_coprime_fp6 (E : EulerSquarePair) :
    IsCoprime E.fm6 E.fp6 := by
  have hN : IsCoprime E.fm6 E.stepN := fm6_coprime_stepN E
  have h3 : IsCoprime E.fm6 (3 : ℤ) := fm6_coprime_three E
  have h12 : IsCoprime E.fm6 (12 : ℤ) :=
    isCoprime_twelve_of_odd_of_isCoprime_three E.fm6_odd h3
  have h12N : IsCoprime E.fm6 ((12 : ℤ) * E.stepN) := h12.mul_right hN
  have h := h12N.mul_add_right_right (z := (1 : ℤ))
  convert h using 1 <;> (simp [fm6, fp6]; ring)

end MazurProof.RationalPointsN12.EulerSquarePair
```

If `simp [fm2, fp2]` or `simp [fm6, fp6]` unfolds too much or too little in the local file, replace the final `convert` lines by explicit equalities:

```lean
  have hfp2 : E.fp2 = (1 : ℤ) * E.fm2 + (4 : ℤ) * E.stepN := by
    simp [fm2, fp2]
    ring
  simpa [hfp2] using h
```

and similarly

```lean
  have hfp6 : E.fp6 = (1 : ℤ) * E.fm6 + (12 : ℤ) * E.stepN := by
    simp [fm6, fp6]
    ring
  simpa [hfp6] using h
```

---

## 4. Square extraction from coprime product

I do **not** know of a stock Mathlib theorem with exactly the requested integer interface:

```lean
x * y = z^2, 0 < x, 0 < y, IsCoprime x y ⟹ x and y are integer squares.
```

The next local theorem should be stated first over `Nat`, then wrapped for positive `Int` factors.  This is the shortest useful frontier:

```lean
/-- Coprime natural factors of a square are squares. -/
theorem Nat.exists_sq_and_sq_of_coprime_mul_eq_sq
    {x y z : ℕ}
    (hcop : x.Coprime y)
    (h : x * y = z ^ 2) :
    ∃ r s : ℕ, x = r ^ 2 ∧ y = s ^ 2 := by
  -- Suggested proof: compare prime multiplicities using `Nat.factorization`.
  -- For every prime p, coprimality gives `x.factorization p = 0` or
  -- `y.factorization p = 0`; the equality to `z^2` gives even valuation
  -- on the nonzero side.  Then use extensionality of factorization.
  -- This is the next genuine local lemma; do not mix it into the AP layer.
  sorry

/-- Positive integer wrapper for coprime factors of a square. -/
theorem Int.exists_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    {x y z : ℤ}
    (hx : 0 < x)
    (hy : 0 < y)
    (hcop : IsCoprime x y)
    (h : x * y = z ^ 2) :
    ∃ r s : ℤ, x = r ^ 2 ∧ y = s ^ 2 := by
  -- Convert to `Nat` using `Int.toNat` or `Int.natAbs`, then use the Nat lemma.
  -- Positivity avoids sign ambiguity for x,y.
  sorry
```

For the immediate `EulerSquarePair` reconstruction, the intended usage after proving the local wrapper is:

```lean
have hmid_prod : E.fm2 * E.fp2 = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 :=
  E.middle_factor_product_square
have hmid_coprime : IsCoprime E.fm2 E.fp2 := fm2_coprime_fp2 E
rcases Int.exists_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    E.fm2_pos E.fp2_pos hmid_coprime hmid_prod with
  ⟨q, r, hq, hr⟩
```

and for the outer pair:

```lean
have hout_prod : E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
  E.outer_factor_product_square
have hout_coprime : IsCoprime E.fm6 E.fp6 := fm6_coprime_fp6 E
rcases Int.exists_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    E.fm6_pos E.fp6_pos hout_coprime hout_prod with
  ⟨p, s, hp, hs⟩
```

Those two `rcases` are the clean next layer after the coprimality theorems above.
