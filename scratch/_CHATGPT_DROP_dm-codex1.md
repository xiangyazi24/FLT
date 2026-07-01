# Q2970 (dm-codex1): direct affine group-law route for `ψ₄` core at `3P`

This answer uses only the self-contained Tate normal form data in the prompt.

Curve:

```text
W : y^2 + (1-c)xy - b y = x^3 - b x^2
```

so

```lean
a1 = 1 - c
 a2 = -b
 a3 = -b
 a4 = 0
 a6 = 0
```

For `Q = 3P = (c, b-c)`, the tangent denominator is exactly

```lean
ψ₂(Q) = 2*(b-c) + (1-c)*c - b = b - c - c^2.
```

Thus your already-proved exact-order consequence

```lean
h6 : b - c - c^2 ≠ 0
```

is precisely the non-vertical-tangent / `Q` not 2-torsion hypothesis needed to use affine doubling formulas.

## Explicit formulas

Let

```lean
d = b - c - c^2
n = 2*c^2 + c - b*c - b
λ = n / d
ν = (b^2 - b*c - c^3) / d
```

where `λ` is the tangent slope at `Q`, and `ν = y_Q - λ*x_Q` is the tangent-line intercept.  Then

```lean
2Q = (x₂, y₂)
```

with

```lean
x₂ = (b - c) * (b^2 - b*c - c^3) / d^2

y₂ = c * (b - c)^2 * (2*b^2 - b*c^2 - 3*b*c + c^2) / d^3
```

The relevant 2-torsion expression at `2Q` is

```lean
ψ₂(2Q) = 2*y₂ + (1-c)*x₂ - b.
```

A direct simplification gives

```lean
ψ₂(2Q) = tatePsi4CoreAt3P(b,c) / d^3.
```

Therefore, if `4Q = 0`, then `2Q` is 2-torsion, so `ψ₂(2Q)=0`; since `d≠0`, this forces

```lean
tatePsi4CoreAt3P(b,c) = 0.
```

No division by `b-c` occurs.  The only affine-doubling denominator is `d = b-c-c^2`.  The hypothesis `c≠0` is not needed for `ψ₄`-core vanishing itself; it is only needed if you later rewrite

```lean
tatePsi4CoreAt3P(b,c) = c * tateC12_K b c
```

and want to divide by `c` to get `tateC12_K b c = 0`.

## Ring/field part: pasteable scratch code

This is the computation layer.  If your file already has `tatePsi4CoreAt3P`, replace `tatePsi4CoreAt3P_scratch` below with the existing name and keep the same proofs, using `simpa [tatePsi4CoreAt3P, ...]` where necessary.

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN12
import Mathlib.Tactic

namespace MazurProof.KubertBridgeN12

noncomputable section

private def tatePsi4CoreAt3P_scratch (b c : ℚ) : ℚ :=
  let b2 : ℚ := (1 - c)^2 - 4*b
  let b4 : ℚ := b*(c - 1)
  let b6 : ℚ := b^2
  let b8 : ℚ := -b^3
  2*c^6 + b2*c^5 + 5*b4*c^4 + 10*b6*c^3 + 10*b8*c^2 +
    (b2*b8 - b4*b6)*c + (b4*b8 - b6^2)

private def tateDoubleDenAt3P_scratch (b c : ℚ) : ℚ :=
  b - c - c^2

private def tateDoubleNumAt3P_scratch (b c : ℚ) : ℚ :=
  2*c^2 + c - b*c - b

private def tateDoubleSlopeAt3P_scratch (b c : ℚ) : ℚ :=
  tateDoubleNumAt3P_scratch b c / tateDoubleDenAt3P_scratch b c

private def tateDoubleInterceptAt3P_scratch (b c : ℚ) : ℚ :=
  (b^2 - b*c - c^3) / tateDoubleDenAt3P_scratch b c

private def tateX2Q_scratch (b c : ℚ) : ℚ :=
  (b - c) * (b^2 - b*c - c^3) /
    (tateDoubleDenAt3P_scratch b c)^2

private def tateY2Q_scratch (b c : ℚ) : ℚ :=
  c * (b - c)^2 * (2*b^2 - b*c^2 - 3*b*c + c^2) /
    (tateDoubleDenAt3P_scratch b c)^3

/-- At `Q=(c,b-c)`, `ψ₂(Q)` is exactly the h6 denominator. -/
private lemma tate_psi2_at_3P_scratch (b c : ℚ) :
    2*(b - c) + (1 - c)*c - b = tateDoubleDenAt3P_scratch b c := by
  dsimp [tateDoubleDenAt3P_scratch]
  ring

/-- Tangent numerator at `Q=(c,b-c)`. -/
private lemma tate_tangent_num_at_3P_scratch (b c : ℚ) :
    3*c^2 + 2*(-b)*c + 0 - (1 - c)*(b - c) =
      tateDoubleNumAt3P_scratch b c := by
  dsimp [tateDoubleNumAt3P_scratch]
  ring

/-- The tangent-line intercept `ν = y_Q - λ*x_Q`. -/
private lemma tate_tangent_intercept_at_3P_scratch
    {b c : ℚ} (hd : tateDoubleDenAt3P_scratch b c ≠ 0) :
    (b - c) - tateDoubleSlopeAt3P_scratch b c * c =
      tateDoubleInterceptAt3P_scratch b c := by
  dsimp [tateDoubleSlopeAt3P_scratch, tateDoubleInterceptAt3P_scratch,
    tateDoubleNumAt3P_scratch, tateDoubleDenAt3P_scratch] at hd ⊢
  field_simp [hd]
  ring

/-- Doubling x-coordinate from `x(2Q)=λ^2+a1*λ-a2-2*x_Q`. -/
private lemma tate_double_x_at_3P_scratch
    {b c : ℚ} (hd : tateDoubleDenAt3P_scratch b c ≠ 0) :
    tateDoubleSlopeAt3P_scratch b c ^ 2 +
        (1 - c) * tateDoubleSlopeAt3P_scratch b c + b - 2*c =
      tateX2Q_scratch b c := by
  dsimp [tateDoubleSlopeAt3P_scratch, tateX2Q_scratch,
    tateDoubleNumAt3P_scratch, tateDoubleDenAt3P_scratch] at hd ⊢
  have hd2 : (b - c - c^2)^2 ≠ 0 := pow_ne_zero 2 hd
  field_simp [hd, hd2]
  ring

/-- Doubling y-coordinate from `y(2Q)=-(λ+a1)*x(2Q)-ν-a3`. -/
private lemma tate_double_y_at_3P_scratch
    {b c : ℚ} (hd : tateDoubleDenAt3P_scratch b c ≠ 0) :
    - (tateDoubleSlopeAt3P_scratch b c + (1 - c)) *
          tateX2Q_scratch b c - tateDoubleInterceptAt3P_scratch b c + b =
      tateY2Q_scratch b c := by
  dsimp [tateDoubleSlopeAt3P_scratch, tateDoubleInterceptAt3P_scratch,
    tateX2Q_scratch, tateY2Q_scratch,
    tateDoubleNumAt3P_scratch, tateDoubleDenAt3P_scratch] at hd ⊢
  have hd2 : (b - c - c^2)^2 ≠ 0 := pow_ne_zero 2 hd
  have hd3 : (b - c - c^2)^3 ≠ 0 := pow_ne_zero 3 hd
  field_simp [hd, hd2, hd3]
  ring

/-- The decisive computation: `ψ₂(2Q)=ψ₄core(Q)/ψ₂(Q)^3`. -/
private lemma tate_double_psi2_core_at_3P_scratch
    {b c : ℚ} (hd : tateDoubleDenAt3P_scratch b c ≠ 0) :
    2 * tateY2Q_scratch b c + (1 - c) * tateX2Q_scratch b c - b =
      tatePsi4CoreAt3P_scratch b c /
        (tateDoubleDenAt3P_scratch b c)^3 := by
  dsimp [tateY2Q_scratch, tateX2Q_scratch, tatePsi4CoreAt3P_scratch,
    tateDoubleDenAt3P_scratch] at hd ⊢
  have hd2 : (b - c - c^2)^2 ≠ 0 := pow_ne_zero 2 hd
  have hd3 : (b - c - c^2)^3 ≠ 0 := pow_ne_zero 3 hd
  field_simp [hd, hd2, hd3]
  ring

/-- Algebraic extraction: if `2Q` is 2-torsion, the core vanishes. -/
private lemma tatePsi4CoreAt3P_eq_zero_of_double_psi2_scratch
    {b c : ℚ} (hd : tateDoubleDenAt3P_scratch b c ≠ 0)
    (hpsi2_2Q :
      2 * tateY2Q_scratch b c + (1 - c) * tateX2Q_scratch b c - b = 0) :
    tatePsi4CoreAt3P_scratch b c = 0 := by
  have hrel := tate_double_psi2_core_at_3P_scratch (b := b) (c := c) hd
  rw [hpsi2_2Q] at hrel
  have hquot :
      tatePsi4CoreAt3P_scratch b c /
        (tateDoubleDenAt3P_scratch b c)^3 = 0 := by
    simpa using hrel.symm
  have hd3 : (tateDoubleDenAt3P_scratch b c)^3 ≠ 0 := pow_ne_zero 3 hd
  have hmul := congrArg
    (fun z : ℚ => z * (tateDoubleDenAt3P_scratch b c)^3) hquot
  field_simp [hd3] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Useful bridge to the `K` polynomial already in `KubertBridgeN12`. -/
private lemma tatePsi4CoreAt3P_eq_c_mul_K_scratch (b c : ℚ) :
    tatePsi4CoreAt3P_scratch b c = c * tateC12_K b c := by
  dsimp [tatePsi4CoreAt3P_scratch, tateC12_K]
  ring

end

end MazurProof.KubertBridgeN12
```

## Group-law glue: Lean-friendly theorem sequence

The preceding lemmas isolate all arithmetic.  The group-law part should be a short wrapper around your existing affine-add/doubling API.

### 1. `Q` is not 2-torsion, so affine tangent doubling applies

```lean
-- `h6` from exact order is exactly this denominator.
have hd : tateDoubleDenAt3P_scratch b c ≠ 0 := by
  simpa [tateDoubleDenAt3P_scratch] using h6

-- Tangent data at Q=(c,b-c):
have hden := tate_psi2_at_3P_scratch b c
have hnum := tate_tangent_num_at_3P_scratch b c
have hnu  := tate_tangent_intercept_at_3P_scratch (b := b) (c := c) hd
have hx2  := tate_double_x_at_3P_scratch (b := b) (c := c) hd
have hy2  := tate_double_y_at_3P_scratch (b := b) (c := c) hd
```

Use these to prove your coordinate lemma for the mathlib affine group law:

```lean
-- Shape only: replace `AffinePoint`/`some`/`affineDouble` by the names in your file.
lemma tate_double_3P_coordinates
    (hb : b ≠ 0) (hd : tateDoubleDenAt3P_scratch b c ≠ 0) :
    2 • Q =
      AffinePoint.some (tateX2Q_scratch b c) (tateY2Q_scratch b c) h2Q_nonsing := by
  -- unfold Q, Tate curve coefficients, affine doubling formula
  -- denominator side condition is `hd`
  -- x-coordinate: `tate_double_x_at_3P_scratch hd`
  -- y-coordinate: `tate_double_y_at_3P_scratch hd`
  -- all remaining goals are `ring`/`field_simp [hd]`
  sorry
```

The important point is that there is no branch split on `b-c`; only the tangent denominator `d=b-c-c^2` is used.

### 2. `4Q=0` forces `ψ₂(2Q)=0`

For any generalized Weierstrass affine point `R=(x,y)`, negation is

```lean
-(x,y) = (x, -y - a1*x - a3).
```

Hence, if `2 • R = 0`, then `R = -R`, and coordinate equality gives

```lean
2*y + a1*x + a3 = 0.
```

For the Tate curve, `a1=1-c`, `a3=-b`, so this becomes

```lean
2*y + (1-c)*x - b = 0.
```

Lean skeleton:

```lean
lemma psi2_eq_zero_of_affine_two_torsion
    {W : WeierstrassCurve ℚ} {x y : ℚ}
    (hxy : (W⁄ℚ).Nonsingular x y)
    (h2 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
    2*y + W.a1*x + W.a3 = 0 := by
  let R : (W⁄ℚ).Point := WeierstrassCurve.Affine.Point.some x y hxy
  have hRadd : R + R = 0 := by
    simpa [R, two_nsmul] using h2
  have hReqNeg : R = -R := by
    calc
      R = R + 0 := by simp
      _ = R + (R + -R) := by simp
      _ = (R + R) + -R := by abel
      _ = 0 + -R := by rw [hRadd]
      _ = -R := by simp
  -- Now simplify affine negation.  In current mathlib this is usually a `simpa`
  -- after unfolding/simping the affine point negation constructor.
  simpa [R, WeierstrassCurve.Affine.Point.neg, add_comm, add_left_comm, add_assoc,
    two_mul] using hReqNeg
```

If the final `simpa` does not find the negation theorem by that name, search for the simp lemma used by your existing affine negation code; the coordinate equation needed is exactly

```lean
y = -y - W.a1*x - W.a3
```

and `ring` turns it into `2*y + W.a1*x + W.a3 = 0`.

Now specialize to `R=2Q`.  Since `4Q=0`, we have `2(2Q)=0`:

```lean
lemma tate_double_3P_psi2_zero_of_fourQ
    (h2Qcoord :
      2 • Q = AffinePoint.some (tateX2Q_scratch b c) (tateY2Q_scratch b c) h2Q)
    (h4Q : (4 : ℕ) • Q = 0) :
    2 * tateY2Q_scratch b c + (1-c) * tateX2Q_scratch b c - b = 0 := by
  have htwo_twoQ :
      (2 : ℕ) • (AffinePoint.some (tateX2Q_scratch b c)
        (tateY2Q_scratch b c) h2Q) = 0 := by
    -- rewrite `2 • (2 • Q)` as `4 • Q`, then use `h4Q`
    simpa [h2Qcoord, two_nsmul, add_assoc] using h4Q
  -- Apply `psi2_eq_zero_of_affine_two_torsion` to the Tate curve.
  -- The Tate coefficients reduce to `a1=1-c`, `a3=-b` by `simp`.
  simpa [tate curve coefficients] using
    psi2_eq_zero_of_affine_two_torsion (W := W) h2Q htwo_twoQ
```

### 3. Final assembly

The final proof is then only the arithmetic extraction lemma:

```lean
theorem tatePsi4CoreAt3P_eq_zero_of_fourQ
    (hb : b ≠ 0)
    (h6 : b - c - c^2 ≠ 0)
    (h2Qcoord :
      2 • Q = AffinePoint.some (tateX2Q_scratch b c) (tateY2Q_scratch b c) h2Q)
    (h4Q : (4 : ℕ) • Q = 0) :
    tatePsi4CoreAt3P_scratch b c = 0 := by
  have hd : tateDoubleDenAt3P_scratch b c ≠ 0 := by
    simpa [tateDoubleDenAt3P_scratch] using h6
  have hpsi2_2Q :
      2 * tateY2Q_scratch b c + (1-c) * tateX2Q_scratch b c - b = 0 :=
    tate_double_3P_psi2_zero_of_fourQ
      (b := b) (c := c) (Q := Q) h2Qcoord h4Q
  exact tatePsi4CoreAt3P_eq_zero_of_double_psi2_scratch
    (b := b) (c := c) hd hpsi2_2Q
```

If your target uses the existing non-scratch name, the last line becomes:

```lean
  have hcore_scratch := tatePsi4CoreAt3P_eq_zero_of_double_psi2_scratch
    (b := b) (c := c) hd hpsi2_2Q
  simpa [tatePsi4CoreAt3P_scratch, tatePsi4CoreAt3P] using hcore_scratch
```

## Direct computation summary

The complete computational identity is:

```lean
2 *
  (c * (b - c)^2 * (2*b^2 - b*c^2 - 3*b*c + c^2) / (b - c - c^2)^3)
+ (1-c) *
  ((b - c) * (b^2 - b*c - c^3) / (b - c - c^2)^2)
- b
=
  tatePsi4CoreAt3P(b,c) / (b - c - c^2)^3.
```

So `4Q=0` supplies the left side as zero, and `b-c-c^2≠0` clears the denominator.  This is the cleanest direct affine route to the `ψ₄`-core residual.
