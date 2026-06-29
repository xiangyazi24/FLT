# Q: FLT N12 residual B bridge to existing quartic descent

## Executive answer

The least-new-code bridge is to make residual `B`

```text
Z^2 = (3*u^2 - v^2) * (u^2 + v^2)
```

produce a primitive non-axis square of the existing quartic

```text
pythagoreanQuarticRhs m n
  = m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4.
```

The bridge must include the nontriviality hypothesis

```text
u^2 ≠ v^2.
```

Without it, `B` has trivial primitive solutions, for example

```text
u = v = 1,  Z = ±2,
```

but the half-sum/half-difference step has one zero leg and cannot produce a non-axis `m*n ≠ 0` solution of `pythagoreanQuarticRhs`.

The exact bridge theorem I would add is:

```lean
/-- Nontrivial primitive residual B produces a primitive opposite-parity square
of the existing N=12 quartic. -/
theorem quartic_B_to_pythagoreanQuarticRhs
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n
```

Then residual `B` is closed by your existing quartic residual package. If the existing theorem has a no-solution shape, the wrapper is:

```lean
theorem quartic_B_only_trivial_of_no_pythagoreanQuarticRhs
    (hQnone : ∀ {m n b : ℤ},
      m * n ≠ 0 → Int.gcd m n = 1 → Odd (m + n) →
      b ^ 2 = pythagoreanQuarticRhs m n → False)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    u ^ 2 = v ^ 2 := by
  by_contra hne
  rcases quartic_B_to_pythagoreanQuarticRhs hcop huv0 hne hB with
    ⟨m,n,b,hmn0,hmn_cop,hmn_par,hq⟩
  exact hQnone hmn0 hmn_cop hmn_par hq
```

If `pythagorean_quartic_residual_reduction` has a reduction/package shape rather than a direct contradiction shape, use `quartic_B_to_pythagoreanQuarticRhs` as the only new bridge and feed the resulting `m,n,b` into the existing reduction chain.

## 1. Residual B theorem DAG

Add the lemmas in this order.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

-- Uses the existing project definition:
-- def pythagoreanQuarticRhs (m n : ℤ) : ℤ :=
--   m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

/-- Residual B. Use as a local abbreviation only if helpful. -/
def QuarticB (u v Z : ℤ) : Prop :=
  Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)

/-- The nontrivial primitive B residual has both variables odd.
This is true even without `huv0`; if a zero case satisfied `hB`, the mod-8
argument plus `hcop` would still contradict it. -/
theorem quartic_B_odd_odd
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hB : QuarticB u v Z) :
    Odd u ∧ Odd v := by
  -- Suggested proof:
  --   `by_cases hu : Even u`; `by_cases hv : Even v`.
  --   both even: contradiction to `hcop`.
  --   u odd, v even: RHS is 3 or 7 mod 8, not a square.
  --   u even, v odd: RHS is 7 mod 8, not a square.
  --   both odd: done.
  -- Use `ZMod 8` and `fin_cases` for square residues `{0,1,4}`.
  sorry

/-- In residual B, after `u,v` are odd, the two factors are twice coprime squares. -/
theorem quartic_B_split_two_squares
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u)
    (hv : Odd v)
    (hB : QuarticB u v Z) :
    ∃ r s : ℤ,
      3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 ∧
      u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
  -- Proof outline:
  --   f := 3*u^2 - v^2, g := u^2 + v^2.
  --   f ≡ 2 mod 8 and g ≡ 2 mod 8.
  --   gcd(f,g)=2, preferably first stated with natAbs if Int.gcd signs hurt.
  --   hB says f*g is a square.
  --   Since g > 0 and f*g = Z^2 ≥ 0, and f ≠ 0, get f > 0.
  --   Then f/2 and g/2 are positive coprime odd integers whose product is a square.
  --   Therefore each half is a square.
  sorry

/-- Half-sum / half-difference decomposition for odd `u,v`, with the exact
primitive and non-axis facts needed later. -/
theorem odd_pair_half_decomposition_primitive
    {u v : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u)
    (hv : Odd v)
    (hne : u ^ 2 ≠ v ^ 2) :
    ∃ R S : ℤ,
      u = R + S ∧
      v = R - S ∧
      R * S ≠ 0 ∧
      Int.gcd R S = 1 ∧
      Odd (R + S) := by
  -- Construct R=(u+v)/2 and S=(u-v)/2.
  -- Oddness gives integrality of the halves.
  -- gcd: a common divisor of R,S divides u=R+S and v=R-S.
  -- nonzero: R=0 gives u=-v, S=0 gives u=v; both contradict hne.
  -- parity: R+S=u is odd.
  sorry

/-- Pythagorean step plus the twist expression. This should be the only lemma
using the signed primitive Pythagorean parametrization. -/
theorem primitive_pythagorean_twist_to_pythagoreanQuarticRhs
    {R S r s : ℤ}
    (hRS0 : R * S ≠ 0)
    (hcop : Int.gcd R S = 1)
    (hpar : Odd (R + S))
    (hs : s ^ 2 = R ^ 2 + S ^ 2)
    (hr : r ^ 2 = R ^ 2 + 4 * R * S + S ^ 2) :
    ∃ m n : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      r ^ 2 = pythagoreanQuarticRhs m n := by
  -- Apply the primitive signed Pythagorean parametrization to
  --   s^2 = R^2 + S^2.
  -- Since gcd(R,S)=1 and Odd(R+S), the legs have opposite parity.
  -- The parametrization gives, up to swap and signs,
  --   one leg = m^2 - n^2,
  --   the other = 2*m*n.
  -- The expression R^2 + 4RS + S^2 is symmetric in R,S.
  -- If the product sign is negative, replace n by -n.
  -- Then use `pythagoreanQuarticRhs_twist_identity` below.
  sorry

/-- Main bridge from residual B to the existing N=12 quartic square. -/
theorem quartic_B_to_pythagoreanQuarticRhs
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hB : QuarticB u v Z) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n := by
  rcases quartic_B_odd_odd hcop hB with ⟨hu, hv⟩
  rcases quartic_B_split_two_squares hcop hu hv hB with ⟨r,s,hr,hs⟩
  rcases odd_pair_half_decomposition_primitive hcop hu hv hne with
    ⟨R,S,huRS,hvRS,hRS0,hRScop,hRSpar⟩

  have hsRS : s ^ 2 = R ^ 2 + S ^ 2 := by
    -- from `u^2+v^2 = 2*s^2`, `u=R+S`, `v=R-S`.
    -- `nlinarith` usually works after the ring identity below.
    subst u
    subst v
    nlinarith [hs, half_sum_diff_sum_sq R S]

  have hrRS : r ^ 2 = R ^ 2 + 4 * R * S + S ^ 2 := by
    -- from `3*u^2-v^2 = 2*r^2`, `u=R+S`, `v=R-S`.
    subst u
    subst v
    nlinarith [hr, half_sum_diff_twist_sq R S]

  rcases primitive_pythagorean_twist_to_pythagoreanQuarticRhs
      hRS0 hRScop hRSpar hsRS hrRS with
    ⟨m,n,hmn0,hmn_cop,hmn_par,hq⟩
  exact ⟨m,n,r,hmn0,hmn_cop,hmn_par,hq⟩

end MazurProof.RationalPointsN12
```

In the actual file, if `QuarticB` is not desired, inline its definition in theorem statements.

## 2. Paste-oriented algebra identities for B

These are the low-risk `ring` lemmas that should be added before the skeleton above.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

-- If the file already has `pythagoreanQuarticRhs`, do not redefine it here.
-- This theorem assumes the existing definition.

lemma half_sum_diff_sum_sq (R S : ℤ) :
    (R + S) ^ 2 + (R - S) ^ 2 = 2 * (R ^ 2 + S ^ 2) := by
  ring

lemma half_sum_diff_twist_sq (R S : ℤ) :
    3 * (R + S) ^ 2 - (R - S) ^ 2 =
      2 * (R ^ 2 + 4 * R * S + S ^ 2) := by
  ring

lemma pythagoreanQuarticRhs_twist_identity (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2
      + 4 * (m ^ 2 - n ^ 2) * (2 * m * n)
      + (2 * m * n) ^ 2
      = pythagoreanQuarticRhs m n := by
  unfold pythagoreanQuarticRhs
  ring

lemma pythagoreanQuarticRhs_twist_identity_neg_right (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2
      - 4 * (m ^ 2 - n ^ 2) * (2 * m * n)
      + (2 * m * n) ^ 2
      = pythagoreanQuarticRhs m (-n) := by
  unfold pythagoreanQuarticRhs
  ring

lemma twist_expr_swap (A B : ℤ) :
    A ^ 2 + 4 * A * B + B ^ 2 = B ^ 2 + 4 * B * A + A ^ 2 := by
  ring

/-- Direct substitution identity for B after half-sum variables. -/
lemma quartic_B_half_substitution (R S : ℤ) :
    ((3 * (R + S) ^ 2 - (R - S) ^ 2)
      * ((R + S) ^ 2 + (R - S) ^ 2))
    = 4 * (R ^ 2 + 4 * R * S + S ^ 2) * (R ^ 2 + S ^ 2) := by
  ring

end MazurProof.RationalPointsN12
```

The identities intentionally avoid `/ 2`. Construct `R,S` once, prove `u=R+S` and `v=R-S`, and then all downstream algebra is pure `ring`/`nlinarith`.

## 3. Finite congruence checks for B

You can prove the parity split with `ZMod 8` in small pieces. Squares mod `8` are `0,1,4`.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

abbrev Z8 := ZMod 8

private lemma z8_square_residue (x : Z8) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  fin_cases x <;> norm_num

private lemma z8_square_ne_three (x : Z8) : x ^ 2 ≠ 3 := by
  intro h
  rcases z8_square_residue x with h0 | h1 | h4
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · rw [h4] at h; norm_num at h

private lemma z8_square_ne_seven (x : Z8) : x ^ 2 ≠ 7 := by
  intro h
  rcases z8_square_residue x with h0 | h1 | h4
  · rw [h0] at h; norm_num at h
  · rw [h1] at h; norm_num at h
  · rw [h4] at h; norm_num at h

/-- If `u` is odd and `v` is even, the B RHS is `3` or `7` mod 8. -/
private lemma quartic_B_rhs_z8_of_odd_even
    {u v : ℤ} (hu : Odd u) (hv : Even v) :
    (((3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) : ℤ) : Z8) = 3 ∨
    (((3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) : ℤ) : Z8) = 7 := by
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  -- Split parity of b; if v^2 ≡ 0 mod 8 get 3, if v^2 ≡ 4 get 7.
  by_cases hb : Even b
  · rcases hb with ⟨t, rfl⟩
    left
    ring_nf
  · have hbodd : Odd b := not_even_iff_odd.mp hb
    rcases hbodd with ⟨t, rfl⟩
    right
    ring_nf

/-- If `u` is even and `v` is odd, the B RHS is `7` mod 8. -/
private lemma quartic_B_rhs_z8_of_even_odd
    {u v : ℤ} (hu : Even u) (hv : Odd v) :
    (((3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) : ℤ) : Z8) = 7 := by
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  by_cases ha : Even a
  · rcases ha with ⟨t, rfl⟩
    ring_nf
  · have haodd : Odd a := not_even_iff_odd.mp ha
    rcases haodd with ⟨t, rfl⟩
    ring_nf

end MazurProof.RationalPointsN12
```

The only brittle API here is the exact spelling of `not_even_iff_odd`; if it differs in the pinned Mathlib, replace it with the local parity theorem already used elsewhere in the file.

## 4. The factor split for B

The split lemma should be isolated because it is the main number-theory step before Pythagorean parametrization.

Recommended support lemmas:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- The two B factors have gcd exactly 2 when `u,v` are coprime odd. -/
/-- Prefer a natAbs version if `Int.gcd` sign normalization is annoying. -/
theorem quartic_B_factor_gcd_eq_two
    {u v : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u)
    (hv : Odd v) :
    Int.gcd (3 * u ^ 2 - v ^ 2) (u ^ 2 + v ^ 2) = 2 := by
  -- Common divisor divides:
  --   (3u^2-v^2) + (u^2+v^2) = 4u^2,
  --   3*(u^2+v^2) - (3u^2-v^2) = 4v^2.
  -- Since gcd(u,v)=1, the gcd divides 4.
  -- Both factors are 2 mod 8, so gcd is exactly 2.
  sorry

/-- Positivity of the first B factor follows from the square equation. -/
theorem quartic_B_first_factor_pos
    {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (hB : QuarticB u v Z) :
    0 < 3 * u ^ 2 - v ^ 2 := by
  -- `u^2 + v^2 > 0` from `huv0`.
  -- If first factor < 0 then RHS < 0, impossible since Z^2 ≥ 0.
  -- If first factor = 0, then `3*u^2=v^2`, impossible for nonzero integers
  -- by a prime/divisibility or mod 3 argument.
  sorry

/-- Coprime square-product split for the B factors. -/
theorem quartic_B_split_two_squares_explicit
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hu : Odd u)
    (hv : Odd v)
    (hB : QuarticB u v Z) :
    ∃ r s : ℤ,
      3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 ∧
      u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
  -- Use the gcd=2 lemma and positivity.
  -- Show Z is even, write Z=2*T.
  -- Then T^2 = ((3u^2-v^2)/2) * ((u^2+v^2)/2).
  -- The two half-factors are coprime positive odd integers.
  -- A coprime product that is a square has square factors.
  sorry

end MazurProof.RationalPointsN12
```

If `Int.gcd ... = 2` is awkward because `Int.gcd` returns a natural coerced into `ℤ` in your local API, use:

```lean
Nat.gcd ((3 * u ^ 2 - v ^ 2).natAbs) ((u ^ 2 + v ^ 2).natAbs) = 2
```

and convert to the needed coprimality of halves.

## 5. Residual A audit

Residual `A`

```text
Z^2 = (u^2 - v^2) * (u^2 + 3*v^2)
```

does **not** appear to be least-new-code reducible to the existing N=12 `pythagoreanQuarticRhs` descent. It is the other 2-cover and naturally leads to an Eisenstein / FLT3-style quartic.

The basic identity is:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma quartic_A_pythagorean_identity (u v Z : ℤ)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  rw [hA]
  ring

/-- Eisenstein quartic naturally produced by residual A. -/
def eisensteinQuarticRhs (r s : ℤ) : ℤ :=
  r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4

lemma eisensteinQuartic_basic_identity (r s : ℤ) :
    (r ^ 2 + s ^ 2) ^ 2 - (r * s) ^ 2 = eisensteinQuarticRhs r s := by
  unfold eisensteinQuarticRhs
  ring

end MazurProof.RationalPointsN12
```

A clean new residual theorem to introduce is either the direct A theorem:

```lean
/-- Direct residual A boundary. -/
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2
```

or the more reusable Eisenstein/FLT3 theorem:

```lean
/-- Eisenstein quartic boundary, equivalent to the classical FLT3 descent. -/
theorem eisensteinQuartic_only_trivial
    {r s C : ℤ}
    (hcop : Int.gcd r s = 1)
    (hrs0 : r * s ≠ 0)
    (hC : C ^ 2 = eisensteinQuarticRhs r s) :
    r ^ 2 = s ^ 2
```

I would add `quartic_A_only_trivial` as the local boundary if the only consumer is `F`. If the repo already has an FLT3/Eisenstein-integer descent, route A through `eisensteinQuartic_only_trivial` instead.

Caution: the previous quick derivation “A gives a primitive Pythagorean triple and hence immediately an Eisenstein quartic” hides parity/gcd cases. The identity

```text
Z^2 + (2*v^2)^2 = (u^2+v^2)^2
```

is always true, but the associated Pythagorean triple may have a common factor `2` when `u,v` are both odd. That is manageable, but it should be handled as a separate parity split rather than assumed primitive.

## 6. False assumptions and safe hypotheses

### B really does force `u,v` odd under gcd and the square equation

This part of the previous answer is correct, with a slightly more precise mod-8 table:

```text
u odd,  v even:
  if v^2 ≡ 0 mod 8, RHS ≡ 3 mod 8;
  if v^2 ≡ 4 mod 8, RHS ≡ 7 mod 8.

u even, v odd:
  RHS ≡ 7 mod 8.

u,v both even:
  impossible from gcd(u,v)=1.

therefore u,v both odd.
```

Squares mod `8` are only `0,1,4`.

### Need `u^2 ≠ v^2` for the bridge to non-axis Q12

Without this, residual B has primitive solutions:

```text
u = v = ±1,      Z = ±2,
u = -v = ±1,     Z = ±2.
```

In these cases one of

```text
R = (u+v)/2,
S = (u-v)/2
```

is zero. The Pythagorean parametrization then has `m*n=0`, which does not match the non-axis hypotheses used by `pythagorean_quartic_residual_reduction` and the signed-cover residual code.

So the bridge theorem must be nontrivial:

```lean
(hne : u ^ 2 ≠ v ^ 2)
```

and the consumer theorem proves `u^2=v^2` by contradiction.

### Need `u*v ≠ 0` for clean positivity and descent statements

The zero cases are actually inconsistent with `hcop` and `hB`, but keeping

```lean
(huv0 : u * v ≠ 0)
```

makes positivity and non-axis statements painless. Since the F-boundary reduction has nonzero variables in the nonzero-X cases, this is a safe hypothesis.

### Do not assume fixed signs in the Pythagorean parametrization

The parametrization of

```text
s^2 = R^2 + S^2
```

gives legs only up to swap and sign. The twist

```text
R^2 + 4*R*S + S^2
```

is symmetric in `R,S`, but it is sensitive to the sign of `R*S`. If the product sign is negative, replace the final quartic parameter `n` by `-n`; this changes

```text
pythagoreanQuarticRhs m n
```

to the required cross-term sign. This is why the Pythagorean bridge theorem should produce `∃ m n`, not try to prescribe them.

## 7. Final least-new-code integration pattern

The direct F-boundary can consume A and B as follows.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- B is closed by existing N=12 quartic machinery. -/
theorem quartic_B_only_trivial_of_existing_Q12
    (hQnone : ∀ {m n b : ℤ},
      m * n ≠ 0 → Int.gcd m n = 1 → Odd (m + n) →
      b ^ 2 = pythagoreanQuarticRhs m n → False)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hB : QuarticB u v Z) :
    u ^ 2 = v ^ 2 := by
  by_contra hne
  rcases quartic_B_to_pythagoreanQuarticRhs hcop huv0 hne hB with
    ⟨m,n,b,hmn0,hmn_cop,hmn_par,hq⟩
  exact hQnone hmn0 hmn_cop hmn_par hq

/-- A remains the only genuinely new arithmetic boundary for the direct F route,
unless the repo already has an Eisenstein/FLT3 descent theorem. -/
theorem F_x_coordinates_of_A_and_existing_Q12
    (hAonly : ∀ {u v Z : ℤ},
      Int.gcd u v = 1 → u * v ≠ 0 →
      Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) →
      u ^ 2 = v ^ 2)
    (hQnone : ∀ {m n b : ℤ},
      m * n ≠ 0 → Int.gcd m n = 1 → Odd (m + n) →
      b ^ 2 = pythagoreanQuarticRhs m n → False) :
    -- replace by the local target statement:
    True := by
  -- Use the existing rational-to-integral/cubic support code.
  -- Squareclass m = u^2      -> A(u,n) -> X=1.
  -- Squareclass m = -3*u^2   -> A(n,u) -> X=-3.
  -- Squareclass m = 3*u^2    -> B(u,n), closed by existing Q12 -> X=3.
  -- Squareclass m = -u^2     -> B(n,u), closed by existing Q12 -> X=-1.
  trivial

end MazurProof.RationalPointsN12
```

Replace `hQnone` by the actual existing theorem if `pythagorean_quartic_residual_reduction` already directly closes primitive opposite-parity squares. If it only packages a residual, the bridge theorem still has the right output: feed `m,n,b` to the existing reduction and then to the already-proved signed/non-axis contradiction chain.

## 8. Best next question

The best next focused question is not about B; B now has a clear bridge to existing code. Ask for A:

```text
Prove the primitive residual
  Z^2 = (u^2 - v^2)*(u^2 + 3*v^2), gcd(u,v)=1, u*v≠0 -> u^2=v^2
in a Lean-friendly way. Handle the parity cases in the Pythagorean identity
  Z^2 + (2*v^2)^2 = (u^2+v^2)^2,
then reduce to the Eisenstein quartic
  C^2 = r^4 - r^2*s^2 + s^4
or directly give an infinite descent.
```

That is the single remaining genuinely new arithmetic residual for the direct elementary F-boundary route.
