# Q2268: Lean plan for `F_N12_AffineEquation` boundary

## Executive recommendation

Do not make `RationalPointsN12.lean` depend on a fully formalized elliptic-curve group, rank, or Selmer-group API. For this file, expose the 2-isogeny descent only through an elementary covering statement over `ℤ`, plus one hard residual theorem classifying four quartic covers.

The current file should consume exactly this shape:

```lean
F_N12_AffineEquation X Y
  ⟹ X = 0 ∨ ∃ d u v z : ℤ,
       d ∈ {-3,-1,1,3}
     ∧ X = d * (u/v)^2
     ∧ z^2 = d*u^4 + 2*u^2*v^2 + (-3/d)*v^4
  ⟹ X ∈ {-3,0,1,-1,3}
```

This is the cleanest Lean boundary between already-available algebra and the remaining mathematics. It avoids formalizing isogenies, Mordell-Weil rank, Selmer exact sequences, and torsion subgroup infrastructure inside the N12 file.

---

## A. Mathematical proof obligation

The curve is

```text
F : y² = x³ + 2x² - 3x = x(x-1)(x+3).
```

It has full rational 2-torsion at `x = -3, 0, 1`, and the visible affine rational points are

```text
(-3,0), (0,0), (1,0), (-1,±2), (3,±6).
```

The desired theorem is exactly that every affine rational point has one of those five `x`-coordinates.

### Recommended residual split

Introduce two residual theorems.

The first theorem is the elementary descent lift. It says that any nonzero affine point lands on one of four quartic homogeneous spaces. This is the part that can be proved with `Rat.num`, `Rat.den`, denominator-square, gcd, and valuations.

The second theorem is the genuinely hard descent classification of those four quartics. It is where the infinite descent, FLT4-style argument, or 2-isogeny descent proof should live.

The four quartics are:

```text
d =  1 : z² =  u⁴ + 2u²v² - 3v⁴ = (u²-v²)(u²+3v²)
d = -1 : z² = -u⁴ + 2u²v² + 3v⁴ = (3v²-u²)(u²+v²)
d =  3 : z² = 3u⁴ + 2u²v² - v⁴ = (3u²-v²)(u²+v²)
d = -3 : z² = -3u⁴ + 2u²v² + v⁴ = (v²-u²)(3u²+v²)
```

The hard classification theorem should prove that a primitive nonzero solution forces `u² = v²`, hence `x = d`, for `d ∈ {-3,-1,1,3}`. The separate case `x = 0` is already one of the boundary values.

### Why this is better than exposing Selmer groups

The 2-isogeny story for

```text
E  : y² = x³ + 2x² - 3x
E' : y² = x³ - 4x² + 16x
```

is mathematically natural. But a literal Lean implementation would need quotient squareclasses, isogeny maps, homogeneous spaces, exactness, rank, torsion, and then a bridge back to affine coordinates. That is far more infrastructure than this file needs.

Instead, let any future isogeny proof establish the two elementary-looking residual theorems below. The N12 file then remains just rational arithmetic plus a small boundary wrapper.

---

## B. Lean wiring that can be added now

The following block is intended to be paste-oriented. If placed in a new file, import the current N12 file instead of redefining `F_N12_AffineEquation`. If placed at the bottom of `RationalPointsN12.lean`, omit the import line that would import itself.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Boundary predicate for the shifted N12 curve. -/
def F_N12_XBoundary (X : ℚ) : Prop :=
  X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3

/-- The right hand side of `F` factors completely over `ℚ`. -/
theorem F_N12_rhs_factor (X : ℚ) :
    X ^ 3 + 2 * X ^ 2 - 3 * X = X * (X - 1) * (X + 3) := by
  ring

/-- Factorized form of the affine equation. -/
theorem F_N12_AffineEquation_factor_iff (X Y : ℚ) :
    F_N12_AffineEquation X Y ↔ Y ^ 2 = X * (X - 1) * (X + 3) := by
  unfold F_N12_AffineEquation
  rw [F_N12_rhs_factor]

/-- The four squareclass representatives that occur in the descent. -/
def F_N12_D (d : ℤ) : Prop :=
  d = -3 ∨ d = -1 ∨ d = 1 ∨ d = 3

/-- Integer value of `-3/d` on the allowed representatives. The fallback `0` is never used
under `F_N12_D d`, but makes the definition total. -/
def F_N12_BoverD (d : ℤ) : ℤ :=
  if d = -3 then 1
  else if d = -1 then 3
  else if d = 1 then -3
  else if d = 3 then -1
  else 0

@[simp] theorem F_N12_BoverD_neg_three : F_N12_BoverD (-3) = 1 := by
  simp [F_N12_BoverD]

@[simp] theorem F_N12_BoverD_neg_one : F_N12_BoverD (-1) = 3 := by
  simp [F_N12_BoverD]

@[simp] theorem F_N12_BoverD_one : F_N12_BoverD 1 = -3 := by
  simp [F_N12_BoverD]

@[simp] theorem F_N12_BoverD_three : F_N12_BoverD 3 = -1 := by
  simp [F_N12_BoverD]

/-- The four descent quartics, uniformly written as
`z² = d*u⁴ + 2*u²*v² + (-3/d)*v⁴`. -/
def F_N12_Quartic (d u v z : ℤ) : Prop :=
  z ^ 2 = d * u ^ 4 + 2 * u ^ 2 * v ^ 2 + F_N12_BoverD d * v ^ 4

/-- A nonzero affine point lifted to one of the four integral quartic covers. -/
def F_N12_QuarticCert (X : ℚ) : Prop :=
  ∃ d u v z : ℤ,
    F_N12_D d ∧
    Nat.Coprime u.natAbs v.natAbs ∧
    u ≠ 0 ∧
    v ≠ 0 ∧
    X = (d : ℚ) * (u : ℚ) ^ 2 / (v : ℚ) ^ 2 ∧
    F_N12_Quartic d u v z

/-- Residual theorem 1: elementary descent lift.

Expected proof ingredients:
* write `X = X.num / X.den` and prove the denominator is a square;
* write `X = m / n²`, `Y = k / n³`, with `Nat.Coprime m.natAbs n.natAbs`;
* obtain `k² = m * (m - n²) * (m + 3*n²)`;
* use pairwise gcd information to prove the squarefree part of `m` is one of
  `-3, -1, 1, 3`;
* write `m = d*u²` and divide by `(d*u)²` to get the quartic equation.
-/
axiom F_N12_descent_lift_to_quartic :
    ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      X = 0 ∨ F_N12_QuarticCert X

/-- Residual theorem 2: classification of the four quartic covers.

This is the hard mathematical theorem. It can be proved by an elementary infinite descent
on the factored quartics, or by a formal 2-isogeny descent packaged to produce this exact
integer statement. -/
axiom F_N12_quartic_solution_residual :
    ∀ {d u v z : ℤ},
      F_N12_D d →
      Nat.Coprime u.natAbs v.natAbs →
      u ≠ 0 →
      v ≠ 0 →
      F_N12_Quartic d u v z →
        (d = -3 ∧ u ^ 2 = v ^ 2) ∨
        (d = -1 ∧ u ^ 2 = v ^ 2) ∨
        (d = 1 ∧ u ^ 2 = v ^ 2) ∨
        (d = 3 ∧ u ^ 2 = v ^ 2)

/-- If `u² = v²`, then the rational `x = d*u²/v²` is just `d`. -/
private theorem F_N12_x_eq_of_int_sq_eq
    {d u v : ℤ} (hv : v ≠ 0) (hsq : u ^ 2 = v ^ 2) :
    (d : ℚ) * (u : ℚ) ^ 2 / (v : ℚ) ^ 2 = (d : ℚ) := by
  have hvq : (v : ℚ) ≠ 0 := by
    exact_mod_cast hv
  have hsqQ : (u : ℚ) ^ 2 = (v : ℚ) ^ 2 := by
    exact_mod_cast hsq
  rw [hsqQ]
  field_simp [hvq]

/-- The quartic residual implies the desired boundary for a certified point. -/
theorem F_N12_boundary_of_quartic_cert {X : ℚ}
    (hcert : F_N12_QuarticCert X) :
    F_N12_XBoundary X := by
  rcases hcert with ⟨d, u, v, z, hd, hcop, hu, hv, hx, hq⟩
  rcases F_N12_quartic_solution_residual hd hcop hu hv hq with hneg3 | hneg1 | hone | hthree
  · rcases hneg3 with ⟨hd', huv⟩
    subst d
    left
    rw [hx]
    exact F_N12_x_eq_of_int_sq_eq (d := -3) hv huv
  · rcases hneg1 with ⟨hd', huv⟩
    subst d
    right; right; right; left
    rw [hx]
    exact F_N12_x_eq_of_int_sq_eq (d := -1) hv huv
  · rcases hone with ⟨hd', huv⟩
    subst d
    right; right; left
    rw [hx]
    exact F_N12_x_eq_of_int_sq_eq (d := 1) hv huv
  · rcases hthree with ⟨hd', huv⟩
    subst d
    right; right; right; right
    rw [hx]
    exact F_N12_x_eq_of_int_sq_eq (d := 3) hv huv

/-- Main boundary theorem for the shifted affine curve. -/
theorem F_N12_AffineEquation_boundary
    {X Y : ℚ} (h : F_N12_AffineEquation X Y) :
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 := by
  rcases F_N12_descent_lift_to_quartic h with hx0 | hcert
  · right; left
    exact hx0
  · exact F_N12_boundary_of_quartic_cert hcert

end RationalPointsN12
end MazurProof
```

### Small algebra lemmas worth adding immediately

These lemmas do not solve the descent, but they make the residual theorem easy to connect to existing branch-to-`F` wrappers.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

@[simp] theorem F_N12_affine_neg_three :
    F_N12_AffineEquation (-3) 0 := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_zero :
    F_N12_AffineEquation 0 0 := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_one :
    F_N12_AffineEquation 1 0 := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_neg_one_pos :
    F_N12_AffineEquation (-1) 2 := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_neg_one_neg :
    F_N12_AffineEquation (-1) (-2) := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_three_pos :
    F_N12_AffineEquation 3 6 := by
  norm_num [F_N12_AffineEquation]

@[simp] theorem F_N12_affine_three_neg :
    F_N12_AffineEquation 3 (-6) := by
  norm_num [F_N12_AffineEquation]

/-- Rational substitution identity behind the quartic cover.
For integral use, instantiate `d,u,v,Y : ℚ`, then prove the left side is an integer square
from the primitive denominator facts. -/
theorem F_N12_squareclass_substitution_identity
    {d u v Y : ℚ}
    (hd : d ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : F_N12_AffineEquation (d * u ^ 2 / v ^ 2) Y) :
    (Y * v ^ 3 / (d * u)) ^ 2 =
      d * u ^ 4 + 2 * u ^ 2 * v ^ 2 - (3 / d) * v ^ 4 := by
  unfold F_N12_AffineEquation at h
  field_simp [hd, hu, hv] at h ⊢
  ring_nf at h ⊢
  exact h

/-- Quartic factorization, `d = 1`. -/
theorem F_N12_quartic_one_factor {u v z : ℤ}
    (h : F_N12_Quartic 1 u v z) :
    z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
  have h' : z ^ 2 = u ^ 4 + 2 * u ^ 2 * v ^ 2 - 3 * v ^ 4 := by
    simpa [F_N12_Quartic, F_N12_BoverD] using h
  rw [h']
  ring

/-- Quartic factorization, `d = -1`. -/
theorem F_N12_quartic_neg_one_factor {u v z : ℤ}
    (h : F_N12_Quartic (-1) u v z) :
    z ^ 2 = (3 * v ^ 2 - u ^ 2) * (u ^ 2 + v ^ 2) := by
  have h' : z ^ 2 = -u ^ 4 + 2 * u ^ 2 * v ^ 2 + 3 * v ^ 4 := by
    simpa [F_N12_Quartic, F_N12_BoverD] using h
  rw [h']
  ring

/-- Quartic factorization, `d = 3`. -/
theorem F_N12_quartic_three_factor {u v z : ℤ}
    (h : F_N12_Quartic 3 u v z) :
    z ^ 2 = (3 * u ^ 2 - v ^ 2) * (u ^ 2 + v ^ 2) := by
  have h' : z ^ 2 = 3 * u ^ 4 + 2 * u ^ 2 * v ^ 2 - v ^ 4 := by
    simpa [F_N12_Quartic, F_N12_BoverD] using h
  rw [h']
  ring

/-- Quartic factorization, `d = -3`. -/
theorem F_N12_quartic_neg_three_factor {u v z : ℤ}
    (h : F_N12_Quartic (-3) u v z) :
    z ^ 2 = (v ^ 2 - u ^ 2) * (3 * u ^ 2 + v ^ 2) := by
  have h' : z ^ 2 = -3 * u ^ 4 + 2 * u ^ 2 * v ^ 2 + v ^ 4 := by
    simpa [F_N12_Quartic, F_N12_BoverD] using h
  rw [h']
  ring

end RationalPointsN12
end MazurProof
```

The connection to any existing branch wrapper is then one line. If an existing lemma has produced

```lean
hF : F_N12_AffineEquation X Y
```

then use

```lean
have hX : X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 :=
  F_N12_AffineEquation_boundary hF
```

No branch-specific descent facts should be duplicated.

---

## C. Exact elementary finite-case reduction statements

Here is the recommended theorem set if you want to prove the lift theorem incrementally rather than as one large residual.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Denominator-square lemma for integral monic Weierstrass equations. -/
axiom F_N12_x_den_is_square :
    ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      ∃ v : ℤ, v ≠ 0 ∧ (X.den : ℤ) = v ^ 2

/-- Squareclass restriction for the numerator of `X`.
This is the key finite squareclass statement. -/
axiom F_N12_x_num_squareclass :
    ∀ {X Y : ℚ}, F_N12_AffineEquation X Y → X ≠ 0 →
      ∃ d u v : ℤ,
        F_N12_D d ∧
        Nat.Coprime u.natAbs v.natAbs ∧
        u ≠ 0 ∧
        v ≠ 0 ∧
        X = (d : ℚ) * (u : ℚ) ^ 2 / (v : ℚ) ^ 2

/-- Integral square lift after the squareclass restriction. -/
axiom F_N12_squareclass_to_integral_quartic :
    ∀ {X Y : ℚ} {d u v : ℤ},
      F_N12_AffineEquation X Y →
      F_N12_D d →
      Nat.Coprime u.natAbs v.natAbs →
      u ≠ 0 →
      v ≠ 0 →
      X = (d : ℚ) * (u : ℚ) ^ 2 / (v : ℚ) ^ 2 →
        ∃ z : ℤ, F_N12_Quartic d u v z

/-- The composed elementary descent lift. -/
theorem F_N12_descent_lift_to_quartic_from_parts
    {X Y : ℚ} (h : F_N12_AffineEquation X Y) :
    X = 0 ∨ F_N12_QuarticCert X := by
  by_cases hx : X = 0
  · exact Or.inl hx
  · rcases F_N12_x_num_squareclass h hx with ⟨d, u, v, hd, hcop, hu, hv, hX⟩
    rcases F_N12_squareclass_to_integral_quartic h hd hcop hu hv hX with ⟨z, hz⟩
    exact Or.inr ⟨d, u, v, z, hd, hcop, hu, hv, hX, hz⟩

end RationalPointsN12
end MazurProof
```

The proof of `F_N12_x_num_squareclass` is elementary and should not require elliptic curves. The core calculation is:

```text
X = m/n²,  Y = k/n³,
gcd(m,n)=1,
k² = m(m-n²)(m+3n²).
```

Then:

```text
gcd(m, m-n²) = 1,
gcd(m, m+3n²) ∣ 3,
gcd(m-n², m+3n²) ∣ 4.
```

Therefore any odd prime other than `3` has even valuation in `m`; the 2-adic valuation of `m` is also even; hence the squarefree part of `m` is one of `±1, ±3`.

That proves the finite rational squareclass reduction. It does not, by itself, classify the quartic solutions.

---

## D. Shorter elementary route?

For this specific curve, the shortest Lean-friendly route is not a literal formal 2-isogeny rank computation. It is the same mathematics expressed as the four quartic covers above.

Reasons:

1. The curve has full rational 2-torsion, so the elementary numerator/denominator descent gives the same squareclass representatives `±1, ±3` without quotienting by `ℚˣ/(ℚˣ)²`.
2. The four quartics factor into products of binary quadratic forms. Their classification can be attacked with `Nat.Coprime`, parity, `Int.gcd`, valuations, and infinite descent.
3. A literal 2-isogeny route would still need to solve the same homogeneous spaces, but it would also require formalizing much more elliptic-curve API.

I would not try to prove the final boundary by only a finite table of modular checks. Each quartic has the known local/global solution with `u² = v²`, so congruences alone cannot simply rule out the whole cover. Some descent or a packaged theorem such as an FLT4/Fermat-right-triangle style residual is needed.

A possible future strengthening is to prove each quartic residual separately:

```lean
axiom F_N12_quartic_one_residual :
    ∀ {u v z : ℤ},
      Nat.Coprime u.natAbs v.natAbs → u ≠ 0 → v ≠ 0 →
      F_N12_Quartic 1 u v z → u ^ 2 = v ^ 2

axiom F_N12_quartic_neg_one_residual :
    ∀ {u v z : ℤ},
      Nat.Coprime u.natAbs v.natAbs → u ≠ 0 → v ≠ 0 →
      F_N12_Quartic (-1) u v z → u ^ 2 = v ^ 2

axiom F_N12_quartic_three_residual :
    ∀ {u v z : ℤ},
      Nat.Coprime u.natAbs v.natAbs → u ≠ 0 → v ≠ 0 →
      F_N12_Quartic 3 u v z → u ^ 2 = v ^ 2

axiom F_N12_quartic_neg_three_residual :
    ∀ {u v z : ℤ},
      Nat.Coprime u.natAbs v.natAbs → u ≠ 0 → v ≠ 0 →
      F_N12_Quartic (-3) u v z → u ^ 2 = v ^ 2
```

Then combine these into `F_N12_quartic_solution_residual` by cases on `F_N12_D d`. This is often easier for Lean because each branch has its own factorization lemma and its own parity/gcd normalization.

---

## E. Suggested implementation order

1. Add `F_N12_XBoundary`, `F_N12_rhs_factor`, `F_N12_D`, `F_N12_BoverD`, `F_N12_Quartic`, and `F_N12_QuarticCert`.
2. Add the two residual axioms or theorem declarations:
   * `F_N12_descent_lift_to_quartic`
   * `F_N12_quartic_solution_residual`
3. Prove the wrapper `F_N12_AffineEquation_boundary` immediately.
4. Replace `F_N12_descent_lift_to_quartic` with the three smaller elementary lemmas once numerator/denominator work is done.
5. Attack the four quartic residuals one at a time, using the factor lemmas.

This gives the current file a stable endpoint now while keeping the hard mathematics isolated in precise, auditable theorem statements.
