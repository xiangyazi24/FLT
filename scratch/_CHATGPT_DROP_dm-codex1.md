# Q2285: Audit of residual A for the N=12 F-boundary descent

Target file: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

The residual under audit is

```lean
-- local abbreviation; delete if the file already has this name/shape
def QuarticA (u v Z : ℤ) : Prop :=
  Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)
```

with `Int.gcd u v = 1` and `u * v ≠ 0`.

## Bottom line

Residual A should **not** be routed to the existing `pythagoreanQuarticRhs` residual unless the existing file already contains a much broader non-axis theorem that includes the Eisenstein/Fermat quartic

```lean
c ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4
```

The natural elementary reduction of A lands exactly in that Eisenstein quartic. That is a genuine new classical residual, essentially the `ℤ[ω]` / FLT3-style descent. The true theorem for A is:

```lean
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2
```

Under `hcop` and `huv0`, the conclusion means the only solutions are the sign variants of `u = ±1`, `v = ±1`, `Z = 0`. The hypothesis `huv0` is necessary: `(u,v,Z) = (1,0,±1)` satisfies A and `Int.gcd u v = 1`, but not `u² = v²`.

---

## 1. Residual theorem to add

Add this as the new hard residual, preferably near the other N=12 residuals. Do **not** install it as an axiom.

```lean
/-- RESIDUAL A / Eisenstein quartic.

Classical content: primitive nonzero integer solutions of
`c² = a⁴ - a² b² + b⁴` are only the equal-square cases `a² = b²`.
This can be proved by descent in Eisenstein integers, or by a classical Fermat
quartic descent after the usual linear change in the equal-parity subcase. -/
-- theorem eisenstein_quartic_square_only_equal_sq
--     {a b c : ℤ}
--     (hcop : Int.gcd a b = 1)
--     (hab0 : a * b ≠ 0)
--     (h : c ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4) :
--     a ^ 2 = b ^ 2
```

A contradiction-oriented equivalent is:

```lean
-- theorem eisenstein_quartic_square_no_nontrivial
--     {a b c : ℤ}
--     (hcop : Int.gcd a b = 1)
--     (hab0 : a * b ≠ 0)
--     (hne : a ^ 2 ≠ b ^ 2) :
--     c ^ 2 ≠ a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4
```

If a local `NonAxisSignedResidual` theorem already includes this exact binary quartic, consume that. If it only covers

```lean
pythagoreanQuarticRhs m n =
  m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2 - 8 * m * n ^ 3 + n ^ 4
```

then it is a B-residual and does not directly consume A.

---

## 2. Paste-oriented algebra lemmas

These can be added now. They are pure `ring`/ordered-ring wrappers.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof
namespace RationalPointsN12

-- Delete this if the file already defines it.
def QuarticA (u v Z : ℤ) : Prop :=
  Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)

@[simp] theorem quarticA_add_four_v_four (u v : ℤ) :
    (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) + (2 * v ^ 2) ^ 2 =
      (u ^ 2 + v ^ 2) ^ 2 := by
  ring

/-- The Pythagorean identity attached to residual A. -/
theorem quarticA_pythagorean_identity
    {u v Z : ℤ}
    (hA : QuarticA u v Z) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  dsimp [QuarticA] at hA
  rw [hA]
  exact quarticA_add_four_v_four u v

/-- Same identity packaged as Mathlib's `PythagoreanTriple`. -/
theorem quarticA_pythagoreanTriple
    {u v Z : ℤ}
    (hA : QuarticA u v Z) :
    PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2) := by
  dsimp [PythagoreanTriple]
  have h := quarticA_pythagorean_identity (u := u) (v := v) (Z := Z) hA
  nlinarith [h]

/-- Positivity of the right factor in A. -/
theorem quarticA_right_factor_pos
    {u v : ℤ}
    (hv0 : v ≠ 0) :
    0 < u ^ 2 + 3 * v ^ 2 := by
  have hv2pos : 0 < v ^ 2 := sq_pos_of_ne_zero v hv0
  have hu2nonneg : 0 ≤ u ^ 2 := sq_nonneg u
  nlinarith

/-- If A is nontrivial, then the left factor is positive. -/
theorem quarticA_left_factor_pos
    {u v Z : ℤ}
    (hv0 : v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    0 < u ^ 2 - v ^ 2 := by
  dsimp [QuarticA] at hA
  have hright : 0 < u ^ 2 + 3 * v ^ 2 := quarticA_right_factor_pos (u := u) (v := v) hv0
  have hprod_nonneg : 0 ≤ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
    rw [← hA]
    exact sq_nonneg Z
  have hleft_nonneg : 0 ≤ u ^ 2 - v ^ 2 := by
    nlinarith
  have hleft_ne : u ^ 2 - v ^ 2 ≠ 0 := sub_ne_zero.mpr hne
  exact lt_of_le_of_ne hleft_nonneg (Ne.symm hleft_ne)

@[simp] theorem eisenstein_sq_sub_sq_add_mul (A B : ℤ) :
    (A ^ 2 - B ^ 2) ^ 2 + A ^ 2 * B ^ 2 =
      A ^ 4 - A ^ 2 * B ^ 2 + B ^ 4 := by
  ring

@[simp] theorem eisenstein_from_half_sum_diff (M N : ℤ) :
    (M - N) ^ 2 + M * N = M ^ 2 - M * N + N ^ 2 := by
  ring

@[simp] theorem eisenstein_from_square_half_sum_diff (A B : ℤ) :
    (A ^ 2 - B ^ 2) ^ 2 + A ^ 2 * B ^ 2 =
      A ^ 4 - A ^ 2 * B ^ 2 + B ^ 4 := by
  ring

/-- Classical Fermat-14 form obtained from the Eisenstein quartic by a linear change. -/
theorem eisenstein_to_fermat14 (m n : ℤ) :
    (m + n) ^ 4 - (m + n) ^ 2 * (m - n) ^ 2 + (m - n) ^ 4 =
      m ^ 4 + 14 * m ^ 2 * n ^ 2 + n ^ 4 := by
  ring

end RationalPointsN12
end MazurProof
```

The prompt's requested identity is exactly `quarticA_pythagorean_identity`:

```lean
Z^2 + (2*v^2)^2 = (u^2+v^2)^2
```

---

## 3. Recommended elementary split route

Let

```lean
A₁ = u ^ 2 - v ^ 2
A₂ = u ^ 2 + 3 * v ^ 2
```

Then `A₂ - A₁ = 4*v²`, and any common divisor of `A₁` and `A₂` divides `4`. Under `Int.gcd u v = 1`:

* if `u` and `v` have opposite parity, then `A₁` and `A₂` are odd and `Int.gcd A₁ A₂ = 1`;
* if `u` and `v` are both odd, then `Int.gcd A₁ A₂ = 4`, and `Int.gcd (A₁ / 4) (A₂ / 4) = 1`.

### 3.1 Product-square splitter interface

Use a local integer wrapper around the standard UFD fact. This is elementary in Mathlib via `Int.natAbs`, `Nat.Coprime`, `IsSquare`, and prime-factorization lemmas, but isolating it avoids API churn.

```lean
/-- Elementary UFD helper: a product of coprime nonnegative integers is a square
only if both factors are squares. -/
-- theorem Int.exists_sq_factors_of_coprime_mul_sq
--     {A B Z : ℤ}
--     (hA0 : 0 ≤ A)
--     (hB0 : 0 ≤ B)
--     (hcop : Int.gcd A B = 1)
--     (h : Z ^ 2 = A * B) :
--     (∃ a : ℤ, A = a ^ 2) ∧ (∃ b : ℤ, B = b ^ 2)
```

Useful checks/searches:

```lean
#check IsSquare
#check IsSquare.mul
#check Nat.Coprime
#check Nat.Coprime.mul_left
#check Nat.Coprime.mul_right
#check Nat.Prime.dvd_of_dvd_pow
```

```bash
grep -R "isSquare.*mul" .lake/packages/mathlib/Mathlib | head -50
grep -R "Coprime.*square" .lake/packages/mathlib/Mathlib | head -50
grep -R "dvd_of_dvd_pow" .lake/packages/mathlib/Mathlib/Data/Nat .lake/packages/mathlib/Mathlib/NumberTheory | head -50
```

### 3.2 Factor gcd statements

```lean
namespace MazurProof
namespace RationalPointsN12

/-- The two A factors differ by `4*v²`. -/
theorem quarticA_factor_diff (u v : ℤ) :
    (u ^ 2 + 3 * v ^ 2) - (u ^ 2 - v ^ 2) = 4 * v ^ 2 := by
  ring

/-- Core gcd divisibility: any common divisor of the A factors divides `4`. -/
-- theorem quarticA_factor_gcd_dvd_four
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1) :
--     Int.gcd (u ^ 2 - v ^ 2) (u ^ 2 + 3 * v ^ 2) ∣ 4

/-- Opposite parity case: both factors are odd, so the gcd is exactly `1`. -/
-- theorem quarticA_factor_gcd_eq_one_of_odd_add
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (hopp : Odd (u + v)) :
--     Int.gcd (u ^ 2 - v ^ 2) (u ^ 2 + 3 * v ^ 2) = 1

/-- Both-odd case: the common factor is exactly `4`. -/
-- theorem quarticA_factor_gcd_eq_four_of_odd_odd
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (hu : Odd u)
--     (hv : Odd v) :
--     Int.gcd (u ^ 2 - v ^ 2) (u ^ 2 + 3 * v ^ 2) = 4

/-- Divided both-odd version, usually the most convenient statement. -/
-- theorem quarticA_factor_gcd_div4_eq_one_of_odd_odd
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (hu : Odd u)
--     (hv : Odd v) :
--     Int.gcd ((u ^ 2 - v ^ 2) / 4) ((u ^ 2 + 3 * v ^ 2) / 4) = 1

/-- With coprime integers, the only parity cases are opposite parity or both odd. -/
-- theorem coprime_int_parity_cases
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1) :
--     Odd (u + v) ∨ (Odd u ∧ Odd v)

end RationalPointsN12
end MazurProof
```

### 3.3 Split lemmas feeding the Eisenstein residual

These theorem interfaces are the clean bridge for the current file.

```lean
/-- Opposite-parity branch of A. -/
-- theorem quartic_A_to_eisenstein_residual_of_odd_add
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (huv0 : u * v ≠ 0)
--     (hopp : Odd (u + v))
--     (hne : u ^ 2 ≠ v ^ 2)
--     (hA : QuarticA u v Z) :
--     ∃ a b : ℤ,
--       Int.gcd a b = 1 ∧
--       a * b ≠ 0 ∧
--       v ^ 2 = (a * b) ^ 2 ∧
--       u ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4

/-- Both-odd branch of A. -/
-- theorem quartic_A_to_eisenstein_residual_of_odd_odd
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (huv0 : u * v ≠ 0)
--     (hu : Odd u)
--     (hv : Odd v)
--     (hne : u ^ 2 ≠ v ^ 2)
--     (hA : QuarticA u v Z) :
--     ∃ a b : ℤ,
--       Int.gcd a b = 1 ∧
--       a * b ≠ 0 ∧
--       v ^ 2 = (a * b) ^ 2 ∧
--       u ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4

/-- Parity-combined elementary bridge from A to the Eisenstein quartic. -/
-- theorem quartic_A_to_eisenstein_residual
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (huv0 : u * v ≠ 0)
--     (hne : u ^ 2 ≠ v ^ 2)
--     (hA : QuarticA u v Z) :
--     ∃ a b : ℤ,
--       Int.gcd a b = 1 ∧
--       a * b ≠ 0 ∧
--       v ^ 2 = (a * b) ^ 2 ∧
--       u ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4
```

Proof sketch for the opposite-parity branch:

1. From `hne`, `huv0`, and `hA`, get `0 < A₁` and `0 < A₂`.
2. From `hopp`, prove both factors are odd.
3. From `quarticA_factor_gcd_eq_one_of_odd_add`, split the product square:

   ```lean
   ∃ r, A₁ = r ^ 2
   ∃ s, A₂ = s ^ 2
   ```

4. Subtract: `s ^ 2 - r ^ 2 = 4 * v ^ 2`.
5. Since `r` and `s` are odd, set `M = (s+r)/2`, `N = (s-r)/2`; prove `M*N = v²`, `r = M-N`, `s = M+N`, and `Int.gcd M N = 1`.
6. Split `M*N = v²` into `M = a²`, `N = b²` up to harmless simultaneous signs.
7. Then

   ```lean
   u ^ 2 = r ^ 2 + v ^ 2
         = (M - N) ^ 2 + M * N
         = M ^ 2 - M * N + N ^ 2
         = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4
   ```

Proof sketch for the both-odd branch:

1. Split after dividing by `4`:

   ```lean
   u ^ 2 - v ^ 2 = 4 * r ^ 2
   u ^ 2 + 3 * v ^ 2 = 4 * s ^ 2
   ```

2. Subtract: `s ^ 2 - r ^ 2 = v ^ 2`.
3. Here `r` and `s` have opposite parity, so `s-r` and `s+r` are odd and coprime. Set `M = s+r`, `N = s-r`.
4. Split `M*N = v²` into squares. Then

   ```lean
   u ^ 2 = 4 * r ^ 2 + v ^ 2
         = (M - N) ^ 2 + M * N
         = M ^ 2 - M * N + N ^ 2
         = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4
   ```

---

## 4. Consumer theorem once the bridge and residual are in scope

This snippet contains no axiom and no `sorry`; it takes the hard residual as a parameter. Replace the parameter with the actual theorem name once proved.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof
namespace RationalPointsN12

theorem quartic_A_only_trivial_of_eisenstein
    (hE : ∀ {a b c : ℤ},
      Int.gcd a b = 1 →
      a * b ≠ 0 →
      c ^ 2 = a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4 →
      a ^ 2 = b ^ 2)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : QuarticA u v Z) :
    u ^ 2 = v ^ 2 := by
  by_cases htriv : u ^ 2 = v ^ 2
  · exact htriv
  · obtain ⟨a, b, habcop, hab0, hv, hu⟩ :=
      quartic_A_to_eisenstein_residual
        (u := u) (v := v) (Z := Z) hcop huv0 htriv hA
    have habsq : a ^ 2 = b ^ 2 :=
      hE (a := a) (b := b) (c := u) habcop hab0 hu
    have hu' : u ^ 2 = a ^ 4 := by
      nlinarith [hu, habsq]
    have hv' : v ^ 2 = a ^ 4 := by
      nlinarith [hv, habsq]
    exact htriv (by nlinarith)

end RationalPointsN12
end MazurProof
```

Once the residual theorem is proved, the final wrapper is:

```lean
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : QuarticA u v Z) :
    u ^ 2 = v ^ 2 := by
  exact quartic_A_only_trivial_of_eisenstein
    (fun {a b c} hcop hab0 h =>
      eisenstein_quartic_square_only_equal_sq
        (a := a) (b := b) (c := c) hcop hab0 h)
    hcop huv0 hA
```

---

## 5. Pythagorean-parametrization route, if desired

The identity also gives a direct Mathlib `PythagoreanTriple` route.

Useful checks:

```lean
#check PythagoreanTriple
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.coprime_classification'
#check PythagoreanTriple.even_odd_of_coprime
```

Expected useful shape:

```lean
-- PythagoreanTriple.coprime_classification'
--   (hpy : PythagoreanTriple x y z) ->
--   Int.gcd x y = 1 ->
--   x % 2 = 1 ->
--   0 < z ->
--   ∃ m n : ℤ,
--     x = m ^ 2 - n ^ 2 ∧
--     y = 2 * m * n ∧
--     z = m ^ 2 + n ^ 2 ∧
--     Int.gcd m n = 1 ∧
--     (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
--     0 ≤ m
```

For opposite parity of `u,v`, the triple is primitive:

```lean
-- theorem quarticA_pythagorean_primitive_of_odd_add
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (hopp : Odd (u + v))
--     (hA : QuarticA u v Z) :
--     Int.gcd Z (2 * v ^ 2) = 1
```

Classification gives `2*v² = 2*m*n` and `u²+v² = m²+n²`, so `m*n = v²`; coprime product-square splitting gives `m = a²`, `n = b²` up to signs, and again `u² = a⁴ - a²*b² + b⁴`.

For both odd `u,v`, divide the Pythagorean triple by `2`:

```lean
-- theorem quarticA_halved_pythagoreanTriple_of_odd_odd
--     {u v Z Z2 C : ℤ}
--     (hu : Odd u)
--     (hv : Odd v)
--     (hZ : Z = 2 * Z2)
--     (hC : u ^ 2 + v ^ 2 = 2 * C)
--     (hA : QuarticA u v Z) :
--     PythagoreanTriple (v ^ 2) Z2 C
```

This is correct, but the factor-splitting route above is generally less case-heavy in Lean.

---

## 6. False shortcuts and sanity checks

* A does **not** immediately force `u² = v²` from sign alone. Sign only proves `u² - v² ≥ 0`, because `u² + 3*v² > 0` and the product is `Z²`.
* If `u² - v² = 0`, then A gives `Z² = 0`, hence `Z = 0`; under `Int.gcd u v = 1` and `u*v ≠ 0`, this is exactly `u² = v² = 1` with arbitrary compatible signs.
* If `u² - v² > 0`, the gcd split produces the Eisenstein quartic. That remaining theorem is nontrivial; treating it as a `ring` or parity consequence would be a false shortcut.
* Small checks agree: `(u,v)=(2,1)` gives `(4-1)*(4+3)=21`, not a square; `(3,1)` gives `8*12=96`, not a square; `(±1,±1)` gives `Z=0`.
* A is the pullback of the F-curve under `X = (u/v)^2`: multiplying `y² = (x²-1)*(x²+3)` by `x²` gives a point on `Y² = X³ + 2*X² - 3*X` with `X=x²`. Proving A by invoking the desired F-boundary theorem would be circular.

---

## Recommended next tasks

1. Add and prove the ring lemmas in section 2 now.
2. Add local wrappers for:

   ```lean
   Int.exists_sq_factors_of_coprime_mul_sq
   quarticA_factor_gcd_eq_one_of_odd_add
   quarticA_factor_gcd_div4_eq_one_of_odd_odd
   coprime_int_parity_cases
   ```

3. Prove `quartic_A_to_eisenstein_residual` using only those wrappers.
4. Treat `eisenstein_quartic_square_only_equal_sq` as the one genuine hard residual for A.
