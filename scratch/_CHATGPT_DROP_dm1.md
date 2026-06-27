# Q1410 / Q1402 (dm1): gcd lemma and quartic descent skeleton

## Q1410: `gcd(h, b^2) = 1`

The clean Lean route is not the long `gcd(a^2-b^2, 2*b^2)` calculation.  Instead, prove the slightly more general division-free lemma:

* if `gcd a b = 1`, and
* `2*h = a^2 - b^2`,

then `gcd h (b^2) = 1`.

The proof is:

1. `gcd a b = 1` gives `IsCoprime a b`.
2. Hence `IsCoprime (a^2) b` by `pow_left`.
3. Since `a^2 = 2*h + b*b`, we get `IsCoprime (2*h + b*b) b`.
4. Strip the `+ b*b` using `IsCoprime.of_add_mul_left_left`, giving `IsCoprime (2*h) b`.
5. Strip the factor `2` using `IsCoprime.mul_left_iff`, giving `IsCoprime h b`.
6. Raise the right side by `pow_right`, giving `IsCoprime h (b^2)`.

Here is the code.

```lean
import Mathlib

namespace DM1

/-- Odd squares have even difference.  This is only needed to connect the
`h = (a^2-b^2)/2` formulation to the division-free lemma below. -/
lemma two_dvd_sq_sub_sq_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    (2 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases ha with ⟨a0, rfl⟩
  rcases hb with ⟨b0, rfl⟩
  refine ⟨2 * (a0 ^ 2 + a0 - b0 ^ 2 - b0), ?_⟩
  ring

/-- The API-light core: no prime-divisor argument is needed. -/
theorem gcd_half_sq_sub_sq_bsq_eq_one_of_twice
    {a b h : ℤ}
    (hab : Int.gcd a b = 1)
    (hh : 2 * h = a ^ 2 - b ^ 2) :
    Int.gcd h (b ^ 2) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]

  have hab' : IsCoprime a b :=
    Int.isCoprime_iff_gcd_eq_one.mpr hab

  have ha2b : IsCoprime (a ^ 2) b := by
    simpa using (hab'.pow_left (m := 2))

  have hrew : a ^ 2 = 2 * h + b * b := by
    rw [hh]
    ring

  have h2hb : IsCoprime (2 * h + b * b) b := by
    simpa [hrew] using ha2b

  have h2hb' : IsCoprime (2 * h) b := by
    exact h2hb.of_add_mul_left_left

  have hhb : IsCoprime h b := by
    exact (IsCoprime.mul_left_iff.mp h2hb').2

  exact hhb.pow_right (n := 2)

/-- The literal `h = (a^2-b^2)/2` version. -/
theorem gcd_sqdiff_div_two_bsq_eq_one
    {a b : ℤ}
    (hab : Int.gcd a b = 1)
    (haodd : Odd a)
    (hbodd : Odd b) :
    Int.gcd ((a ^ 2 - b ^ 2) / 2) (b ^ 2) = 1 := by
  apply gcd_half_sq_sub_sq_bsq_eq_one_of_twice (a := a) (b := b)
  · exact hab
  · have h_even : (2 : ℤ) ∣ a ^ 2 - b ^ 2 :=
      two_dvd_sq_sub_sq_of_odd haodd hbodd
    calc
      2 * ((a ^ 2 - b ^ 2) / 2)
          = ((a ^ 2 - b ^ 2) / 2) * 2 := by ring
      _ = a ^ 2 - b ^ 2 := Int.ediv_mul_cancel h_even

/-- Same result, stated with an explicit named integer `h`.  Positivity is
included to match the descent context, though the gcd proof itself does not use it. -/
theorem gcd_h_bsq_eq_one
    {a b h : ℤ}
    (_ha_pos : 0 < a)
    (_hb_pos : 0 < b)
    (haodd : Odd a)
    (hbodd : Odd b)
    (hab : Int.gcd a b = 1)
    (hh : h = (a ^ 2 - b ^ 2) / 2) :
    Int.gcd h (b ^ 2) = 1 := by
  subst h
  exact gcd_sqdiff_div_two_bsq_eq_one
    (a := a) (b := b) hab haodd hbodd

```

## Q1402: quartic descent step skeleton

This skeleton keeps the hard mathematical substeps isolated as named `sorry`s.  The new gcd lemma above is exactly the primitive-Pythagorean input.

```lean
import Mathlib

namespace DM1

/-- The quartic relation used in the descent.  `QuarticPlus r B s` means
`s^2 = r^4 + r^2 B^2 - B^4`. -/
def QuarticPlus (r B s : ℤ) : Prop :=
  s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- This is the orientation of the primitive Pythagorean classification needed
for the descent.  It packages the parity/orientation work:
from `h^2 + (b^2)^2 = r^2` and `gcd(h,b^2)=1`, choose the classification branch
where the odd leg `b^2` is `m^2-n^2`. -/
lemma pythagorean_oriented_for_odd_square
    {h b r : ℤ}
    (hbodd : Odd b)
    (hpyth : PythagoreanTriple h (b ^ 2) r)
    (hcop : Int.gcd h (b ^ 2) = 1) :
    ∃ m n : ℤ,
      h = 2 * m * n ∧
      b ^ 2 = m ^ 2 - n ^ 2 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by
  have hprim : hpyth.IsPrimitiveClassified := by
    exact hpyth.isPrimitiveClassified_of_coprime hcop
  -- Hard but standard orientation step:
  -- `b` odd implies `b^2` is odd; in the primitive classification, the odd leg
  -- is the difference-of-squares leg, not the `2*m*n` leg.
  rcases hprim with ⟨m, n, hmn, hmn_coprime, hmn_parity⟩
  sorry

/-- Square splitting substep: if `b^2 = (m-n)(m+n)` and the two factors are
coprime positive odd integers, then each is a square.  The signs/orientation are
packed into the statement to keep the descent core readable. -/
lemma split_odd_square_factors
    {b m n : ℤ}
    (hbpos : 0 < b)
    (hbmn : b ^ 2 = m ^ 2 - n ^ 2)
    (hmn_coprime : Int.gcd m n = 1)
    (hmn_parity : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    ∃ u v : ℤ,
      0 < u ∧
      1 < v ∧
      b = u * v ∧
      m - n = u ^ 2 ∧
      m + n = v ^ 2 := by
  -- Hard substeps:
  -- 1. Rewrite `m^2-n^2 = (m-n)(m+n)`.
  -- 2. Prove `Int.gcd (m-n) (m+n) = 1` using coprimality and parity.
  -- 3. Since their product is `b^2`, each factor is a square up to sign.
  -- 4. Use positivity/orientation to choose positive `u,v`.
  sorry

/-- Core descent skeleton.

Input relation:
`a^4 + 5 b^4 = 4 r^2 + 2 a^2 b^2`.

Then
`4 r^2 = (a^2-b^2)^2 + 4 b^4`.
For odd `a,b`, set `h=(a^2-b^2)/2`, giving
`r^2 = h^2 + (b^2)^2`.
Primitive classification plus square splitting produces `b = u v`, and the
new solution is `QuarticPlus v u a`, i.e.
`a^2 = v^4 + v^2 u^2 - u^4`.
-/
theorem quartic_descent_step_core_skeleton
    {a b r : ℤ}
    (hapos : 0 < a)
    (hbpos : 0 < b)
    (haodd : Odd a)
    (hbodd : Odd b)
    (hab : Int.gcd a b = 1)
    (hrel : a ^ 4 + 5 * b ^ 4 = 4 * r ^ 2 + 2 * a ^ 2 * b ^ 2) :
    ∃ u v : ℤ,
      0 < u ∧
      1 < v ∧
      b = u * v ∧
      QuarticPlus v u a ∧
      u < b := by
  let h : ℤ := (a ^ 2 - b ^ 2) / 2

  have hh_twice : 2 * h = a ^ 2 - b ^ 2 := by
    dsimp [h]
    have h_even : (2 : ℤ) ∣ a ^ 2 - b ^ 2 :=
      two_dvd_sq_sub_sq_of_odd haodd hbodd
    calc
      2 * ((a ^ 2 - b ^ 2) / 2)
          = ((a ^ 2 - b ^ 2) / 2) * 2 := by ring
      _ = a ^ 2 - b ^ 2 := Int.ediv_mul_cancel h_even

  have hgcd_h_b2 : Int.gcd h (b ^ 2) = 1 := by
    dsimp [h]
    exact gcd_sqdiff_div_two_bsq_eq_one
      (a := a) (b := b) hab haodd hbodd

  have h_four :
      4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
    -- Mechanical algebra from `hrel`.
    -- Suggested proof: `ring_nf at hrel ⊢; linarith` or a `linear_combination`
    -- after normalizing `(a*b)^2` to `a^2*b^2`.
    sorry

  have hpyth : PythagoreanTriple h (b ^ 2) r := by
    -- Use `hh_twice` and `h_four`, then divide by `4` algebraically.
    -- Target unfolds to `h*h + b^2*b^2 = r*r`.
    dsimp [PythagoreanTriple]
    sorry

  obtain ⟨m, n, h_h, hb2_mn, hmn_coprime, hmn_parity⟩ :=
    pythagorean_oriented_for_odd_square hbodd hpyth hgcd_h_b2

  obtain ⟨u, v, hu_pos, hv_gt_one, hb_uv, hmn_sub, hmn_add⟩ :=
    split_odd_square_factors hbpos hb2_mn hmn_coprime hmn_parity

  refine ⟨u, v, hu_pos, hv_gt_one, hb_uv, ?_, ?_⟩

  · -- New quartic solution: `QuarticPlus v u a`.
    -- From `m-n=u^2`, `m+n=v^2`, get:
    --   `2*m = u^2+v^2`, `2*n = v^2-u^2`.
    -- From `h=2mn` and `h=(a^2-b^2)/2`, get:
    --   `a^2 = b^2 + 2h`.
    -- Substitute `b=uv`, `h=2mn`, and the formulas for `m,n`:
    --   `a^2 = u^2 v^2 + v^4 - u^4`.
    -- This is exactly `QuarticPlus v u a`.
    dsimp [QuarticPlus]
    sorry

  · -- Descent of the second parameter.
    -- Since `b = u*v`, `u > 0`, and `v > 1`, we have `u < b`.
    sorry

end DM1
```

The key point for downstream formalization is that Q1410 should be used as `gcd_h_bsq_eq_one` or, even better, the division-free `gcd_half_sq_sub_sq_bsq_eq_one_of_twice` when you already have `2*h = a^2-b^2` in the local context.
