# Q: FLT N12 residual B bridge to existing quartic descent

## Short answer

The least-new-code bridge is to prove that every **nontrivial** primitive solution of

```text
B(u,v,Z):  Z^2 = (3*u^2 - v^2) * (u^2 + v^2)
```

produces a primitive opposite-parity square of the existing N=12 quartic

```text
pythagoreanQuarticRhs m n
  = m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4.
```

The safe bridge theorem is:

```lean
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

Then `B` is closed by contradiction using the existing non-axis N=12 quartic residual code. The theorem should not try to prove `B` has no primitive solutions: it has trivial primitive solutions with `u^2=v^2`, e.g. `u=v=1`, `Z=±2`. Those are exactly the cases giving `X=3` or `X=-1` in the direct `F` boundary.

Residual `A`

```text
A(u,v,Z):  Z^2 = (u^2 - v^2) * (u^2 + 3*v^2)
```

does **not** appear to reduce to the existing N=12 `pythagoreanQuarticRhs` machinery with little code. It naturally reduces to an Eisenstein / FLT3 quartic. The clean local boundary for `A` is either direct:

```lean
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2
```

or reusable:

```lean
def eisensteinQuarticRhs (r s : ℤ) : ℤ :=
  r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4

theorem eisensteinQuartic_only_trivial
    {r s C : ℤ}
    (hcop : Int.gcd r s = 1)
    (hrs0 : r * s ≠ 0)
    (hC : C ^ 2 = eisensteinQuarticRhs r s) :
    r ^ 2 = s ^ 2
```

## 1. Exact theorem interfaces for residual B

These signatures are intended to sit under `namespace MazurProof.RationalPointsN12` in `RationalPointsN12.lean`, using the existing definition `pythagoreanQuarticRhs`.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Optional local abbreviation for residual B. -/
def QuarticB (u v Z : ℤ) : Prop :=
  Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)

/-- Squares modulo 8. Useful for the parity split. -/
private lemma zmod8_square_residue (x : ZMod 8) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  fin_cases x <;> norm_num

/-- Primitive residual B forces both variables odd. -/
theorem quartic_B_odd_odd
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hB : QuarticB u v Z) :
    Odd u ∧ Odd v := by
  -- Proof plan:
  --   split on Even u / Even v.
  --   both even contradict `Int.gcd u v = 1`.
  --   odd/even gives RHS ≡ 3 or 7 mod 8.
  --   even/odd gives RHS ≡ 7 mod 8.
  --   squares mod 8 are only 0,1,4.
  -- Keep this as a separate lemma; it is pure finite arithmetic.
  sorry

/-- The two B-factors have gcd exactly 2 when `u,v` are coprime odd. -/
theorem quartic_B_factor_gcd_eq_two
    {u v : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u)
    (hv : Odd v) :
    Int.gcd (3 * u ^ 2 - v ^ 2) (u ^ 2 + v ^ 2) = 2 := by
  -- Any common divisor divides
  --   (3u^2-v^2) + (u^2+v^2) = 4u^2
  --   3*(u^2+v^2) - (3u^2-v^2) = 4v^2.
  -- Coprimality gives gcd | 4.
  -- Both factors are 2 mod 8, hence gcd is exactly 2.
  -- If Int.gcd normalization is awkward, prove the natAbs version instead.
  sorry

/-- Split residual B into two half-square equations. -/
theorem quartic_B_split_two_squares
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hu : Odd u)
    (hv : Odd v)
    (hB : QuarticB u v Z) :
    ∃ r s : ℤ,
      3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 ∧
      u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
  -- Let f=3u^2-v^2 and g=u^2+v^2.
  -- f,g are 2 mod 8 and gcd(f,g)=2.
  -- hB says f*g is a square.
  -- g>0. From f*g=Z^2 and f≠0, get f>0.
  -- f=0 would imply v^2=3u^2, impossible for nonzero integers.
  -- Then f/2 and g/2 are coprime positive odd integers whose product is a square.
  -- Conclude both are squares.
  sorry

/-- Odd coprime `u,v` decompose as `u=R+S`, `v=R-S`, with primitive
opposite-parity nonzero legs when `u^2 ≠ v^2`. -/
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
  -- Oddness gives integrality.
  -- A common divisor of R,S divides u=R+S and v=R-S.
  -- R=0 gives u=-v; S=0 gives u=v; both contradict hne.
  -- Odd (R+S) is just Odd u.
  sorry

/-- Signed primitive Pythagorean parametrization plus the N=12 twist.
This is the only theorem that should know about the Pythagorean parametrization API. -/
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
  -- Apply primitive signed Pythagorean parametrization to `s^2=R^2+S^2`.
  -- Since gcd(R,S)=1 and Odd(R+S), R,S are opposite parity.
  -- The legs are, up to swap/sign,
  --   m^2 - n^2 and 2*m*n.
  -- The expression `R^2 + 4RS + S^2` is symmetric under swapping R,S.
  -- If the product sign is negative, replace n by -n and use the negative-cross-term identity.
  sorry

/-- Least-new-code bridge: nontrivial primitive residual B produces a primitive
opposite-parity square of the existing N=12 quartic. -/
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
  rcases quartic_B_split_two_squares hcop huv0 hu hv hB with ⟨r, s, hr, hs⟩
  rcases odd_pair_half_decomposition_primitive hcop hu hv hne with
    ⟨R, S, huRS, hvRS, hRS0, hRScop, hRSpar⟩

  have hsRS : s ^ 2 = R ^ 2 + S ^ 2 := by
    -- from `u^2+v^2 = 2*s^2`, `u=R+S`, `v=R-S`.
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
    ⟨m, n, hmn0, hmn_cop, hmn_par, hq⟩
  exact ⟨m, n, r, hmn0, hmn_cop, hmn_par, hq⟩

end MazurProof.RationalPointsN12
```

If the existing residual theorem uses an explicit predicate rather than the four side conditions, add a thin adapter:

```lean
-- Example shape only; replace `PythagoreanQuarticResidual` with the local name.
theorem quartic_B_to_existing_pythagorean_residual
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    ∃ m n b : ℤ,
      m * n ≠ 0 ∧ Int.gcd m n = 1 ∧ Odd (m + n) ∧
      b ^ 2 = pythagoreanQuarticRhs m n :=
  quartic_B_to_pythagoreanQuarticRhs hcop huv0 hne hB
```

Then the close-by-existing-code theorem is:

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
    ⟨m, n, b, hmn0, hmn_cop, hmn_par, hq⟩
  exact hQnone hmn0 hmn_cop hmn_par hq
```

If `pythagorean_quartic_residual_reduction` does not directly prove `False` but produces `NonAxisSignedResidual` / `NonAxisFactorIdentityResidual`, the bridge output above is still the correct input: feed `m,n,b` into the existing reduction package and then into the already available branch-to-`F` contradiction or residual closer.

## 2. Paste-oriented algebra identities for B

These should compile with only `ring` once `pythagoreanQuarticRhs` is in scope.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma half_sum_diff_sum_sq (R S : ℤ) :
    (R + S) ^ 2 + (R - S) ^ 2 = 2 * (R ^ 2 + S ^ 2) := by
  ring

lemma half_sum_diff_twist_sq (R S : ℤ) :
    3 * (R + S) ^ 2 - (R - S) ^ 2 =
      2 * (R ^ 2 + 4 * R * S + S ^ 2) := by
  ring

lemma quartic_B_half_substitution (R S : ℤ) :
    ((3 * (R + S) ^ 2 - (R - S) ^ 2)
      * ((R + S) ^ 2 + (R - S) ^ 2))
      = 4 * (R ^ 2 + 4 * R * S + S ^ 2) * (R ^ 2 + S ^ 2) := by
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

end MazurProof.RationalPointsN12
```

The important implementation detail is: avoid integer division in the main bridge. Prove a construction lemma that gives `R,S` with

```text
u = R+S,  v = R-S.
```

Then all algebra after that is `ring` or `nlinarith`.

## 3. Finite congruence/parity checks for B

Residual `B` really does force `u,v` odd under `Int.gcd u v = 1` and `hB`. More precise mod-8 table:

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

Paste-oriented helper statements:

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

private lemma quartic_B_rhs_z8_of_odd_even
    {u v : ℤ} (hu : Odd u) (hv : Even v) :
    (((3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) : ℤ) : Z8) = 3 ∨
    (((3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) : ℤ) : Z8) = 7 := by
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  by_cases hb : Even b
  · rcases hb with ⟨t, rfl⟩
    left
    ring_nf
  · have hbodd : Odd b := not_even_iff_odd.mp hb
    rcases hbodd with ⟨t, rfl⟩
    right
    ring_nf

end MazurProof.RationalPointsN12
```

The exact theorem name `not_even_iff_odd` may vary in the pinned Mathlib. If it fails, use the local parity conversion already present in `RationalPointsN12.lean`.

## 4. Residual A: what to do

Residual `A`

```text
Z^2 = (u^2 - v^2) * (u^2 + 3*v^2)
```

has the universal identity

```text
Z^2 + (2*v^2)^2 = (u^2 + v^2)^2.
```

Lean:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma quartic_A_pythagorean_identity (u v Z : ℤ)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  rw [hA]
  ring

/-- Natural Eisenstein/FLT3 quartic for residual A. -/
def eisensteinQuarticRhs (r s : ℤ) : ℤ :=
  r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4

lemma eisensteinQuartic_basic_identity (r s : ℤ) :
    (r ^ 2 + s ^ 2) ^ 2 - (r * s) ^ 2 = eisensteinQuarticRhs r s := by
  unfold eisensteinQuarticRhs
  ring

end MazurProof.RationalPointsN12
```

I do **not** see a low-code bridge from A to the existing `pythagoreanQuarticRhs` residual. The natural endpoint is an Eisenstein/FLT3 descent. Introduce one of these two boundaries:

```lean
/-- Direct residual A boundary. -/
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2
```

or, if the repo has or wants reusable FLT3/Eisenstein infrastructure:

```lean
/-- Eisenstein quartic boundary, classically handled by FLT3 descent. -/
theorem eisensteinQuartic_only_trivial
    {r s C : ℤ}
    (hcop : Int.gcd r s = 1)
    (hrs0 : r * s ≠ 0)
    (hC : C ^ 2 = eisensteinQuarticRhs r s) :
    r ^ 2 = s ^ 2
```

Caution: the step from `quartic_A_pythagorean_identity` to an Eisenstein quartic has parity/gcd branches. If `u,v` are both odd, the Pythagorean triple has a common factor `2`. Do not assume primitive parametrization without splitting this case.

## 5. False assumptions / safe hypotheses

### B has trivial primitive solutions

`B` is not a no-solution theorem. For example:

```text
u = v = 1:
(3*u^2 - v^2) * (u^2 + v^2) = 2 * 2 = 4 = (±2)^2.
```

Similarly `u=-v=±1` works. Therefore the theorem closing B should conclude

```text
u^2 = v^2
```

not `False`.

### The bridge to Q12 needs `u^2 ≠ v^2`

When `u^2=v^2`, one of

```text
R = (u+v)/2,
S = (u-v)/2
```

is zero. The resulting Pythagorean parametrization has `m*n=0`, which does not match the non-axis hypotheses for the existing N=12 quartic residual code. So include:

```lean
(hne : u ^ 2 ≠ v ^ 2)
```

in `quartic_B_to_pythagoreanQuarticRhs`.

### Keep `u*v ≠ 0`

The zero cases are inconsistent with `hcop` and `hB`, but `u*v ≠ 0` is available from the direct F-boundary reduction and keeps positivity/non-axis lemmas simple. Keep it in bridge theorems.

### Do not prescribe signs in the Pythagorean output

The primitive Pythagorean parametrization returns legs only up to signs and swap. Because the twist expression is sensitive to the sign of `R*S`, the bridge should produce `∃ m n`, and should use either

```lean
pythagoreanQuarticRhs_twist_identity m n
```

or

```lean
pythagoreanQuarticRhs_twist_identity_neg_right m n
```

as needed.

## 6. Integration with existing architecture

The direct `F` boundary should use:

```lean
theorem quartic_B_only_trivial_of_existing_Q12
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
    ⟨m, n, b, hmn0, hmn_cop, hmn_par, hq⟩
  exact hQnone hmn0 hmn_cop hmn_par hq
```

If your existing theorem is not a direct `hQnone`, adapt it as:

```lean
-- Pseudocode shape, replacing names by actual checked wrappers.
theorem no_pythagoreanQuarticRhs_from_existing_reductions
    {m n b : ℤ}
    (hmn0 : m * n ≠ 0)
    (hcop : Int.gcd m n = 1)
    (hpar : Odd (m + n))
    (hq : b ^ 2 = pythagoreanQuarticRhs m n) :
    False := by
  -- pythagorean_quartic_residual_reduction hmn0 hcop hpar hq
  -- rational_kubert_cover_residual_reduction / signed residual wrappers
  -- NonAxisSignedResidual -> NonAxisFactorIdentityResidual -> branch-to-F contradiction
  sorry
```

Then direct `F` routing is:

```text
squareclass m =  u^2    -> residual A(u,n) -> X=1,
squareclass m = -3*u^2  -> residual A(n,u) -> X=-3,
squareclass m =  3*u^2  -> residual B(u,n) -> existing Q12 -> X=3,
squareclass m = -u^2    -> residual B(n,u) -> existing Q12 -> X=-1.
```

Thus only residual A remains new for the direct elementary route.
