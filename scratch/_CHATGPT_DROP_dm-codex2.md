# Q: FLT N12 direct elementary affine-boundary audit

## Source check

I attempted to inspect the GitHub-visible file named in the prompt:

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
```

on branch `scratch`. The GitHub connector returned `Not Found`, and repository code search did not find `RationalPointsN12`. I therefore treat the local file path `/Users/huangx/repos/flt-ai/FLT/Assumptions/MazurProof/RationalPointsN12.lean` as ahead of, or different from, the GitHub-visible branch. The route below is stated against the equation itself and uses names intended to paste under `namespace MazurProof.RationalPointsN12`.

## Executive answer

The point list is correct. The rational affine solutions of

```text
F : Y^2 = X^3 + 2*X^2 - 3*X = X*(X-1)*(X+3)
```

have

```text
X ∈ {-3, 0, 1, -1, 3},
```

with the corresponding `Y` values

```text
(-3,0), (0,0), (1,0), (-1,±2), (3,±6).
```

There is a direct elementary reduction from a rational point to primitive integer quartics. However, it does **not** give a one-line gcd/congruence proof. After clearing denominators and using the full rational 2-torsion factorization, the problem reduces to two primitive quartic residuals:

```text
A(u,v,Z):  Z^2 = (u^2 - v^2) * (u^2 + 3*v^2),
B(u,v,Z):  Z^2 = (3*u^2 - v^2) * (u^2 + v^2),
```

with `gcd(u,v)=1` and nonzero variables. To finish the affine theorem it suffices to prove:

```text
A(u,v,Z) -> u^2 = v^2,
B(u,v,Z) -> u^2 = v^2.
```

Those quartic residuals are exactly the elementary shadow of the 2-isogeny descent. Solving them directly is possible by classical infinite descent, but it is not obviously shorter in Lean than the specialized 2-isogeny route. The single hardest residual is `B`: its mod-8 split leads back to the same N=12 non-axis quartic/descent pattern already appearing elsewhere in this project.

So the best Lean-friendly elementary route is:

```text
rational point on F
  -> primitive integral cubic equation
  -> squareclass support m ∈ {u^2, -u^2, 3u^2, -3u^2}
  -> quartic residual A or B
  -> quartic residual theorem
  -> X ∈ {-3,0,1,-1,3}.
```

If the project wants the shortest boundary statement, use the two quartic residual theorems as the arithmetic boundary. If the project wants a proof with no boundary theorem, the 2-isogeny descent remains the cleaner global organization.

## 1. Point-list sanity check

The five `X` values give exactly the expected `Y` values:

```text
X = -3:  X*(X-1)*(X+3) = 0,
X =  0:  X*(X-1)*(X+3) = 0,
X =  1:  X*(X-1)*(X+3) = 0,
X = -1:  (-1)*(-2)*(2) = 4,
X =  3:  3*2*6 = 36.
```

A tiny Lean check:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

private def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

lemma F_N12_rhs_factor (X : ℚ) :
    X ^ 3 + 2 * X ^ 2 - 3 * X = X * (X - 1) * (X + 3) := by
  ring

example : F_N12_AffineEquation (-3) 0 := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation 0 0 := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation 1 0 := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation (-1) 2 := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation (-1) (-2) := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation 3 6 := by norm_num [F_N12_AffineEquation]
example : F_N12_AffineEquation 3 (-6) := by norm_num [F_N12_AffineEquation]

end MazurProof.RationalPointsN12
```

## 2. Clear denominators to the primitive cubic residual

For a rational affine point, use the standard monic-cubic denominator lemma. There are integers `m,n,W` with

```text
n ≠ 0,
gcd(m,n)=1,
X = m / n^2,
Y = W / n^3,
W^2 = m*(m - n^2)*(m + 3*n^2).                    (Cubic)
```

This is the first exact integer residual.

Lean statement:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

private def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- Pure `field_simp` identity once `X=m/n^2`, `Y=W/n^3` are chosen. -/
lemma F_N12_clear_denoms_identity
    (m n W : ℤ) (hn : n ≠ 0) :
    (((W : ℚ) / (n : ℚ)^3)^2 =
      ((m : ℚ) / (n : ℚ)^2)^3
        + 2 * ((m : ℚ) / (n : ℚ)^2)^2
        - 3 * ((m : ℚ) / (n : ℚ)^2)) ↔
    W ^ 2 = m * (m - n ^ 2) * (m + 3 * n ^ 2) := by
  constructor <;> intro h
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnq] at h
    norm_num at h
    -- The remaining goal is a polynomial rearrangement over `ℤ` cast to `ℚ`.
    -- In-file this usually closes by `norm_num` + `ring_nf at h ⊢`.
    -- Replace this placeholder by the local tactic sequence that works with casts.
    sorry
  · have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnq]
    norm_num
    -- Same cast/ring cleanup as above.
    sorry

/-- Standard monic-cubic denominator-square lemma specialized to `F`. -/
/-
theorem F_N12_rat_to_integral_cubic
    {X Y : ℚ} (hF : F_N12_AffineEquation X Y) :
    ∃ m n W : ℤ,
      n ≠ 0 ∧ Int.gcd m n = 1 ∧
      X = (m : ℚ) / (n : ℚ)^2 ∧
      Y = (W : ℚ) / (n : ℚ)^3 ∧
      W ^ 2 = m * (m - n ^ 2) * (m + 3 * n ^ 2)
-/

end MazurProof.RationalPointsN12
```

I wrote the clearing identity with `sorry` comments because cast normalization varies by local imports; the mathematical content is a single `field_simp` plus `ring`. In the actual file, it is better to prove the polynomial identity first over `ℚ`, then move the integer-cast equality through `norm_num`.

## 3. GCD structure of the primitive cubic residual

Assume

```text
W^2 = m*(m-n^2)*(m+3*n^2),
gcd(m,n)=1.
```

The factor gcds are:

```text
gcd(m, m-n^2) = 1,
gcd(m, m+3*n^2) | 3,
gcd(m-n^2, m+3*n^2) | 4.
```

More precisely:

```text
gcd(m, m-n^2) = gcd(m,n^2) = 1,
gcd(m, m+3*n^2) = gcd(m,3),
gcd(m-n^2, m+3*n^2) | 4.
```

Important warning: the three factors are **not** pairwise coprime in general. For example, with `m=3,n=1`, the factors are

```text
m = 3,
m-n^2 = 2,
m+3*n^2 = 6,
```

and the first and third share `3`. With `m,n` both odd, the last two factors can share powers of `2`. Therefore a route that declares all three factors to be squares is false.

The useful consequence is only a squareclass support statement for `m`: every prime `p ≠ 3` dividing `m` has even valuation. Thus, if `m ≠ 0`, there is an integer `u` such that

```text
m =  u^2,
   or m = -u^2,
   or m =  3*u^2,
   or m = -3*u^2.                                  (Support)
```

This is exactly the support restriction for the 2-descent map `x mod squares`, but it is obtained here by elementary gcd/valuation arithmetic.

Lean statements:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma gcd_m_m_sub_nsq
    {m n : ℤ} (hcop : Int.gcd m n = 1) :
    Int.gcd m (m - n ^ 2) = 1 := by
  -- `gcd(m, m-n^2)=gcd(m,n^2)=1`.
  sorry

lemma gcd_m_m_add_three_nsq_dvd_three
    {m n : ℤ} (hcop : Int.gcd m n = 1) :
    Int.gcd m (m + 3 * n ^ 2) ∣ 3 := by
  -- Common divisor divides `3*n^2`; coprime to `n`, hence divides `3`.
  sorry

lemma gcd_m_sub_m_add_three_dvd_four
    {m n : ℤ} (hcop : Int.gcd m n = 1) :
    Int.gcd (m - n ^ 2) (m + 3 * n ^ 2) ∣ 4 := by
  -- Difference is `4*n^2`; common divisor is coprime to `n`.
  sorry

/-- Squareclass support of the numerator `m`. This is the elementary form of
`δ(F(ℚ)) ⊆ {1,-1,3,-3}`. -/
/-
theorem cubic_residual_m_squareclass_support
    {m n W : ℤ}
    (hcop : Int.gcd m n = 1)
    (hm0 : m ≠ 0)
    (hW : W ^ 2 = m * (m - n ^ 2) * (m + 3 * n ^ 2)) :
    ∃ u : ℤ,
      m = u ^ 2 ∨ m = -u ^ 2 ∨ m = 3 * u ^ 2 ∨ m = -3 * u ^ 2
-/

end MazurProof.RationalPointsN12
```

The support theorem is most naturally proved by prime valuations. A no-valuation version is possible but messier: repeatedly use Euclid's lemma on prime divisors of `m` and the square product.

## 4. The two quartic residuals

Define:

```text
A(u,v,Z) : Z^2 = (u^2 - v^2)*(u^2 + 3*v^2),
B(u,v,Z) : Z^2 = (3*u^2 - v^2)*(u^2 + v^2).
```

Substituting the four possible squareclasses for `m` into `(Cubic)` gives only these two residual forms.

### Case `m = u^2`

```text
W^2 = u^2 * (u^2 - n^2) * (u^2 + 3*n^2).
```

After proving `u | W`, write `W=u*Z` and get

```text
Z^2 = (u^2 - n^2)*(u^2 + 3*n^2) = A(u,n,Z).
```

If `A` only has the trivial primitive solutions `u^2=n^2`, then

```text
X = m/n^2 = u^2/n^2 = 1.
```

### Case `m = -3*u^2`

```text
W^2 = 9*u^2 * (n^2 - u^2) * (n^2 + 3*u^2).
```

Write `W=3*u*Z` and get

```text
Z^2 = (n^2 - u^2)*(n^2 + 3*u^2) = A(n,u,Z).
```

Then `n^2=u^2`, so

```text
X = -3*u^2/n^2 = -3.
```

### Case `m = 3*u^2`

```text
W^2 = 9*u^2 * (3*u^2 - n^2) * (u^2 + n^2).
```

Write `W=3*u*Z` and get

```text
Z^2 = (3*u^2 - n^2)*(u^2 + n^2) = B(u,n,Z).
```

Then `u^2=n^2`, so

```text
X = 3.
```

### Case `m = -u^2`

```text
W^2 = u^2 * (u^2 + n^2) * (3*n^2 - u^2).
```

Write `W=u*Z` and get

```text
Z^2 = (3*n^2 - u^2)*(n^2 + u^2) = B(n,u,Z).
```

Then `n^2=u^2`, so

```text
X = -1.
```

The substitution identities are pure `ring` facts:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma cubic_subst_pos_one (u n : ℤ) :
    (u ^ 2) * (u ^ 2 - n ^ 2) * (u ^ 2 + 3 * n ^ 2)
      = u ^ 2 * ((u ^ 2 - n ^ 2) * (u ^ 2 + 3 * n ^ 2)) := by
  ring

lemma cubic_subst_neg_three (u n : ℤ) :
    (-3 * u ^ 2) * ((-3 * u ^ 2) - n ^ 2) * ((-3 * u ^ 2) + 3 * n ^ 2)
      = (3 * u) ^ 2 * ((n ^ 2 - u ^ 2) * (n ^ 2 + 3 * u ^ 2)) := by
  ring

lemma cubic_subst_pos_three (u n : ℤ) :
    (3 * u ^ 2) * ((3 * u ^ 2) - n ^ 2) * ((3 * u ^ 2) + 3 * n ^ 2)
      = (3 * u) ^ 2 * ((3 * u ^ 2 - n ^ 2) * (u ^ 2 + n ^ 2)) := by
  ring

lemma cubic_subst_neg_one (u n : ℤ) :
    (-u ^ 2) * ((-u ^ 2) - n ^ 2) * ((-u ^ 2) + 3 * n ^ 2)
      = u ^ 2 * ((3 * n ^ 2 - u ^ 2) * (n ^ 2 + u ^ 2)) := by
  ring

/-- Integer square cancellation helper. Mathlib may already have this as a
`pow_dvd_pow_iff`/`sq_dvd_sq` variant; isolate the API here. -/
/-
theorem exists_sq_factor_of_sq_eq_sq_mul
    {W u A : ℤ} (hu : u ≠ 0)
    (h : W ^ 2 = u ^ 2 * A) :
    ∃ Z : ℤ, W = u * Z ∧ Z ^ 2 = A
-/

end MazurProof.RationalPointsN12
```

The helper `exists_sq_factor_of_sq_eq_sq_mul` is true for integers by prime valuations: from `u^2 | W^2`, get `u | W`; substitute `W=u*Z` and cancel `u^2` in the integral domain.

## 5. Boundary residual statements that imply the affine theorem

These are the cleanest elementary residuals to consume from Lean:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Residual A: the squareclass `1`/`-3` quartic has only the trivial primitive
solutions relevant to the curve. -/
/-
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2
-/

/-- Residual B: the squareclass `3`/`-1` quartic has only the trivial primitive
solutions relevant to the curve. -/
/-
theorem quartic_B_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    u ^ 2 = v ^ 2
-/

/-- Reduction of the affine X-coordinate theorem to the two quartic residuals. -/
/-
theorem F_N12_x_coordinates_of_quartic_residuals
    (hAonly : ∀ {u v Z : ℤ},
      Int.gcd u v = 1 -> u * v ≠ 0 ->
      Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) ->
      u ^ 2 = v ^ 2)
    (hBonly : ∀ {u v Z : ℤ},
      Int.gcd u v = 1 -> u * v ≠ 0 ->
      Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) ->
      u ^ 2 = v ^ 2) :
    ∀ {X Y : ℚ}, F_N12_AffineEquation X Y ->
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3
-/

end MazurProof.RationalPointsN12
```

This is probably the most useful Lean boundary if the goal is to avoid explicit Mordell-Weil/rank formalization.

## 6. How to attack residual A

Residual A is

```text
Z^2 = (u^2 - v^2)*(u^2 + 3*v^2),
gcd(u,v)=1,
u*v ≠ 0.                                             (A)
```

A useful identity is

```text
Z^2 + (2*v^2)^2 = (u^2 + v^2)^2.                    (A-Pyth)
```

Indeed:

```text
(u^2+v^2)^2 - Z^2
= u^4 + 2u^2v^2 + v^4 - (u^4 + 2u^2v^2 - 3v^4)
= 4v^4.
```

So any nontrivial A-solution gives a Pythagorean triangle whose even leg is `2*v^2`. Primitive Pythagorean parametrization splits `v^2 = r*s` with `gcd(r,s)=1`, hence `r=r0^2`, `s=s0^2`. This reduces A to the classical Eisenstein/Fermat quartic

```text
C^2 = r0^4 - r0^2*s0^2 + s0^4.                     (Eis)
```

The trivial A-solutions correspond to `r0^2=s0^2` and then `u^2=v^2`.

Lean identities:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma quartic_A_pythagorean_identity (u v Z : ℤ)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  rw [hA]
  ring

lemma eisenstein_quartic_identity (r s : ℤ) :
    (r ^ 2 - s ^ 2) ^ 2 + (r * s) ^ 2
      = r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4 := by
  ring

/-- Classical Fermat/Eisenstein residual that would close residual A. -/
/-
theorem eisenstein_quartic_square_only_trivial
    {r s C : ℤ}
    (hcop : Int.gcd r s = 1)
    (hrs0 : r * s ≠ 0)
    (hC : C ^ 2 = r ^ 4 - r ^ 2 * s ^ 2 + s ^ 4) :
    r ^ 2 = s ^ 2
-/

end MazurProof.RationalPointsN12
```

This is a known classical infinite descent, closely related to the elementary proof of FLT exponent `3` in `ℤ[ω]`. If the repo already has an FLT3 or Eisenstein-integer descent component, residual A should be routed there.

## 7. How to attack residual B

Residual B is

```text
Z^2 = (3*u^2 - v^2)*(u^2 + v^2),
gcd(u,v)=1,
u*v ≠ 0.                                             (B)
```

A quick mod-8 analysis shows a nontrivial solution must have `u,v` both odd.

If `u` and `v` have opposite parity, then:

```text
u odd,  v even -> RHS ≡ 3 * 1 * 1 = 3 mod 8,
u even, v odd  -> RHS ≡ (-1) * 1 = 7 mod 8,
```

not a square. Both even is excluded by gcd. Hence both are odd.

For odd coprime `u,v`, the two factors in B satisfy

```text
3*u^2 - v^2 ≡ 2 mod 8,
u^2 + v^2   ≡ 2 mod 8,
gcd(3*u^2 - v^2, u^2 + v^2) = 2.
```

Therefore the halves are coprime odd squares:

```text
3*u^2 - v^2 = 2*r^2,
u^2 + v^2   = 2*s^2.                              (Bsplit)
```

Set

```text
R = (u+v)/2,
S = (u-v)/2.
```

Then

```text
s^2 = R^2 + S^2,
r^2 = R^2 + 4*R*S + S^2.                            (Btwist)
```

Parametrizing the primitive Pythagorean equation `s^2=R^2+S^2` produces

```text
r^2 = p^4 + 8*p^3*q + 2*p^2*q^2 - 8*p*q^3 + q^4.   (Q12)
```

This is precisely the N=12 quartic square equation that appears in the non-axis signed-cover descent. Thus direct residual B is not an elementary shortcut; it is the same hard descent in a different coordinate system.

Lean statements:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma quartic_B_opposite_parity_impossible
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    ¬ ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) := by
  -- Cast to `ZMod 8` or use `% 8`; squares are `0,1,4` mod 8.
  sorry

lemma quartic_B_split
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (hu : Odd u) (hv : Odd v)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    ∃ r s : ℤ,
      3 * u ^ 2 - v ^ 2 = 2 * r ^ 2 ∧
      u ^ 2 + v ^ 2 = 2 * s ^ 2 := by
  -- The two factors are `2 mod 8`, have gcd `2`, and their product is a square.
  sorry

lemma quartic_B_half_sum_id_1 (u v : ℤ) :
    u ^ 2 + v ^ 2 = 2 * (((u + v) / 2) ^ 2 + ((u - v) / 2) ^ 2) := by
  -- This exact statement needs parity hypotheses for `/`; better introduce
  -- `R S` by equations `u=R+S`, `v=R-S` in Lean.
  sorry

lemma quartic_B_twist_identity (R S : ℤ) :
    3 * (R + S) ^ 2 - (R - S) ^ 2
      = 2 * (R ^ 2 + 4 * R * S + S ^ 2) := by
  ring

/-- The N=12 quartic produced from the Pythagorean parametrization. -/
def Q12 (p q : ℤ) : ℤ :=
  p ^ 4 + 8 * p ^ 3 * q + 2 * p ^ 2 * q ^ 2 - 8 * p * q ^ 3 + q ^ 4

lemma pythagorean_twist_to_Q12_identity (p q : ℤ) :
    (p ^ 2 - q ^ 2) ^ 2
      + 4 * (p ^ 2 - q ^ 2) * (2 * p * q)
      + (2 * p * q) ^ 2
      = Q12 p q := by
  unfold Q12
  ring

end MazurProof.RationalPointsN12
```

In Lean, do not use integer division by `2` in the main theorem if avoidable. Instead, after `u,v` are odd, introduce integers `R,S` satisfying

```text
u = R + S,
v = R - S
```

using `R=(u+v)/2`, `S=(u-v)/2` only in a construction lemma. The identities then become pure `ring`.

## 8. Final theorem skeleton consuming the residuals

This is the intended final Lean shape for the direct route:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

private def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- X-coordinate version requested in Q2271, reduced to two elementary quartic residuals. -/
/-
theorem F_N12_x_coordinates
    (hAonly : ∀ {u v Z : ℤ},
      Int.gcd u v = 1 -> u * v ≠ 0 ->
      Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) ->
      u ^ 2 = v ^ 2)
    (hBonly : ∀ {u v Z : ℤ},
      Int.gcd u v = 1 -> u * v ≠ 0 ->
      Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) ->
      u ^ 2 = v ^ 2)
    {X Y : ℚ}
    (hF : F_N12_AffineEquation X Y) :
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 := by
  -- 1. Use `F_N12_rat_to_integral_cubic` to get m,n,W.
  -- 2. If m=0, then X=0.
  -- 3. Otherwise use `cubic_residual_m_squareclass_support`.
  -- 4. Four squareclass cases:
  --    m= u^2    -> A(u,n) -> X=1.
  --    m=-3u^2  -> A(n,u) -> X=-3.
  --    m= 3u^2  -> B(u,n) -> X=3.
  --    m=-u^2   -> B(n,u) -> X=-1.
  sorry
-/

end MazurProof.RationalPointsN12
```

This theorem is deliberately parameterized by the two quartic residual solvers. That lets you integrate the denominator/gcd/squareclass work now and postpone the genuinely hard descent.

## 9. Why this is not shorter than 2-isogeny descent

The full 2-torsion factorization gives a nice elementary numerator squareclass support statement, but that statement only says

```text
X mod squares ∈ {1,-1,3,-3}.
```

It does **not** determine `X`. The remaining condition is exactly the solvability of the homogeneous spaces represented by A and B. Solving A and B is what a 2-descent does.

The specialized 2-isogeny route has an advantage: the dual curve

```text
F' : Y^2 = X^3 - 4X^2 + 16X
```

has squareclass support `{1,2}`, and the nontrivial class `2` is killed immediately by the mod-16 lemma

```text
W^2 ≠ 2*m^4 - 4*m^2*n^2 + 8*n^4
```

for primitive `m,n`. This is shorter than proving both A and B directly from scratch.

So my adversarial conclusion is:

```text
A direct elementary route exists, but the first genuinely hard residual is quartic_B_only_trivial.
The cleanest proof of quartic_B_only_trivial is essentially the N=12 descent already under discussion.
```

## 10. The single hardest residual left

The hardest residual to dispatch next is:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Hard residual B. This is the direct-factorization shadow of the N=12 descent. -/
/-
theorem quartic_B_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hB : Z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2)) :
    u ^ 2 = v ^ 2
-/

end MazurProof.RationalPointsN12
```

The next best ChatGPT question is:

```text
Prove the primitive integer residual
  Z^2 = (3*u^2 - v^2)*(u^2 + v^2), gcd(u,v)=1, u*v≠0 -> u^2=v^2,
by a Lean-friendly infinite descent. Start with the mod-8 proof that u,v are odd, split the two 2 mod 8 factors into 2*squares, set R=(u+v)/2 and S=(u-v)/2, and show how the resulting Pythagorean parametrization gives a strictly smaller solution or reduces to the existing N=12 Q12 residual.
```

If that residual is accepted as a boundary, the requested `X ∈ {-3,0,1,-1,3}` theorem becomes mostly denominator clearing, gcd support, four `ring` substitutions, and rational arithmetic.
