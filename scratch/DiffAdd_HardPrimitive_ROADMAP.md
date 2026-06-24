[ask-gpt dm1 tid=e90fdf72 +0s] dispatched, waiting for answer
[ask-gpt dm1 tid=e90fdf72 +90s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +180s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +270s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +360s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +450s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +540s] waiting (status=processing)
[ask-gpt dm1 tid=e90fdf72 +563s] terminal: status=completed
I cannot honestly give a verified paste-and-compile proof for your exact `scratch/Seam2.lean`: the connected repo search does not expose `SameP1`, `XOnly.diffAddRep`, or `xRep_add_of_xRep_sub`, so I cannot see your actual constructor names or simp-normal forms. But the proof below is the one I would implement. The key point is that the affine core should **not** be proved by expanding both additions independently inside the main theorem. Prove the symmetric sum identity once, then package projectively.

Mathlib already exposes the relevant primitives: `Point.add_some`, `Point.add_of_Y_eq`, `Point.add_self_of_Y_eq`, `Point.xRep_zero`, `Point.xRep_some`, `Point.xRep_neg`, `slope`, `addX`, `negY`, and the useful x-only theorem `addX_eq_addX_negY_sub`; the docs also confirm `xRep 0 = ![1,0]` and affine `xRep = ![x,1]`. citeturn902414view3turn902414view4 The formula file gives `addX = ℓ^2 + a₁ℓ - a₂ - x₁ - x₂`, `negY x y = -y-a₁x-a₃`, and the slope split lemmas including `slope_of_X_ne`. citeturn553107view0turn553107view1

## 1. Add these projective packaging helpers

Adjust only the namespace/field names if your `SameP1` constructor has a different spelling. I assume your definition is literally:

```lean
def SameP1 (v w : Fin 2 → k) : Prop :=
  ∃ u : kˣ, w = u • v
```

Then use:

```lean
namespace SameP1

variable {k : Type*} [Field k]

lemma refl (v : Fin 2 → k) : SameP1 v v := by
  refine ⟨1, ?_⟩
  ext i
  simp

lemma affine_of_eq_div
    {x X Z : k}
    (hZ : Z ≠ 0)
    (hx : x = X / Z) :
    SameP1 ![x, 1] ![X, Z] := by
  refine ⟨Units.mk0 Z hZ, ?_⟩
  ext i <;> fin_cases i
  · simp [hx]
    field_simp [hZ]
  · simp

lemma affine_of_num_eq
    {x X Z : k}
    (hZ : Z ≠ 0)
    (hX : X = Z * x) :
    SameP1 ![x, 1] ![X, Z] := by
  refine ⟨Units.mk0 Z hZ, ?_⟩
  ext i <;> fin_cases i <;> simp [hX, mul_comm]

lemma infty
    {X : k}
    (hX : X ≠ 0) :
    SameP1 ![(1 : k), 0] ![X, 0] := by
  refine ⟨Units.mk0 X hX, ?_⟩
  ext i <;> fin_cases i <;> simp

end SameP1
```

## 2. Prove the affine symmetric identity once

This is the core algebra. Notice it uses the **sum form**

\[
x(A+B)+x(A-B)=
\frac{2x_Ax_B(x_A+x_B)+b_2x_Ax_B+b_4(x_A+x_B)+b_6}{(x_A-x_B)^2}.
\]

The `field_simp` list is just the secant denominator. The curve equations enter through `linear_combination`.

```lean
namespace WeierstrassCurve.Affine.XOnly

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve k)

lemma addX_sum_mul_sq_of_X_ne
    {x₁ x₂ y₁ y₂ : k}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    ((W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)
      + W.toAffine.addX x₁ x₂
          (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
      * (x₁ - x₂)^2)
      =
      2 * x₁ * x₂ * (x₁ + x₂)
        + W.b₂ * x₁ * x₂
        + W.b₄ * (x₁ + x₂)
        + W.b₆ := by
  have hden : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx

  rw [W.toAffine.slope_of_X_ne hx]
  rw [W.toAffine.slope_of_X_ne hx]

  rw [W.toAffine.equation_iff] at h₁ h₂

  field_simp [hden]

  linear_combination
    (norm := ring_nf [
      WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY
    ])
    2 * h₁ + 2 * h₂
```

This is the exact place where the two curve equations kill the \(y_1^2\) and \(y_2^2\) terms. After clearing denominators, the numerator is precisely

```lean
2 * (h₁.left - h₁.right) + 2 * (h₂.left - h₂.right)
```

up to `ring_nf`.

You also need the vertical specialization:

```lean
lemma vertical_num_eq_psi_sq
    {x y : k}
    (h : W.toAffine.Equation x y) :
    4 * x^3
      + W.b₂ * x^2
      + 2 * W.b₄ * x
      + W.b₆
      =
      (y - W.toAffine.negY x y)^2 := by
  rw [W.toAffine.equation_iff] at h
  linear_combination
    (norm := ring_nf [
      WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,
      WeierstrassCurve.Affine.negY
    ])
    -4 * h

end WeierstrassCurve.Affine.XOnly
```

Here

\[
y-\operatorname{negY}(x,y)=2y+a_1x+a_3,
\]

so this is the usual identity

\[
(2y+a_1x+a_3)^2
=
4x^3+b_2x^2+2b_4x+b_6.
\]

## 3. Main theorem, with cases

This is the actual proof structure. I am writing it against the names you gave: `XOnly.Δ`, `XOnly.diffAddNum`, `XOnly.diffAddDen`, `XOnly.diffAddRep`. If your `XOnly` namespace stores the core numerator separately, replace the repeated expression by that local abbreviation.

```lean
open WeierstrassCurve
open WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.XOnly

variable {k : Type*} [Field k] [DecidableEq k]

theorem xRep_add_of_xRep_sub
    (W : WeierstrassCurve k) [W.IsElliptic]
    (A B : W.toAffine.Point)
    (hsub : A - B ≠ 0) :
    SameP1
      ((A + B).xRep)
      (XOnly.diffAddRep W A.xRep B.xRep (A - B).xRep) := by
  classical

  rcases A with _ | ⟨x₁, y₁, h₁ns⟩
  · -- A = O
    rcases B with _ | ⟨x₂, y₂, h₂ns⟩
    · -- O - O = O, excluded.
      exfalso
      exact hsub (by simp)
    · -- O + B = B, O - B = -B, and xRep(-B)=xRep(B).
      simpa [
        sub_eq_add_neg,
        XOnly.diffAddRep,
        XOnly.diffAddNum,
        XOnly.diffAddDen,
        XOnly.Δ,
        XOnly.X,
        XOnly.Z,
        WeierstrassCurve.Affine.Point.xRep_zero,
        WeierstrassCurve.Affine.Point.xRep_some,
        WeierstrassCurve.Affine.Point.xRep_neg
      ] using
        (SameP1.refl (![x₂, (1 : k)]))

  · -- A affine
    rcases B with _ | ⟨x₂, y₂, h₂ns⟩
    · -- B = O
      simpa [
        sub_eq_add_neg,
        XOnly.diffAddRep,
        XOnly.diffAddNum,
        XOnly.diffAddDen,
        XOnly.Δ,
        XOnly.X,
        XOnly.Z,
        WeierstrassCurve.Affine.Point.xRep_zero,
        WeierstrassCurve.Affine.Point.xRep_some,
        WeierstrassCurve.Affine.Point.xRep_neg
      ] using
        (SameP1.refl (![x₁, (1 : k)]))

    · -- both affine
      have h₁eq : W.toAffine.Equation x₁ y₁ := h₁ns.1
      have h₂eq : W.toAffine.Equation x₂ y₂ := h₂ns.1

      by_cases hx : x₁ = x₂
      · -- Same x-coordinate. Then either A = B or A = -B.
        rcases W.toAffine.Y_eq_of_X_eq h₁eq h₂eq hx with hy_same | hy_neg
        · -- A = B, hence A - B = 0, contradiction.
          exfalso
          apply hsub
          subst x₂
          subst y₂
          simp

        · -- A = -B, so A + B = O.
          have hABzero :
              (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
                + Point.some x₂ y₂ h₂ns = 0 := by
            exact Point.add_of_Y_eq hx hy_neg

          -- If A were 2-torsion, then A - B = A + A = 0,
          -- contradiction. Hence the vertical numerator is nonzero.
          have hpsi_ne : y₁ ≠ W.toAffine.negY x₁ y₁ := by
            intro hpsi
            apply hsub

            have hnegB :
                -(Point.some x₂ y₂ h₂ns : W.toAffine.Point)
                  =
                Point.some x₁ y₁ h₁ns := by
              subst x₂
              simp [Point.neg_some, hy_neg]

            calc
              (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
                  - Point.some x₂ y₂ h₂ns
                  =
                Point.some x₁ y₁ h₁ns
                  + (-(Point.some x₂ y₂ h₂ns : W.toAffine.Point)) := by
                    simp [sub_eq_add_neg]
              _ =
                Point.some x₁ y₁ h₁ns + Point.some x₁ y₁ h₁ns := by
                    rw [hnegB]
              _ = 0 := by
                    exact Point.add_self_of_Y_eq hpsi

          have hN :
              4 * x₁^3
                + W.b₂ * x₁^2
                + 2 * W.b₄ * x₁
                + W.b₆
                ≠ 0 := by
            have hsq :=
              XOnly.vertical_num_eq_psi_sq (W := W) h₁eq
            rw [hsq]
            exact sq_ne_zero (sub_ne_zero.mpr hpsi_ne)

          rcases hD : (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
                        - Point.some x₂ y₂ h₂ns with _ | ⟨xD, yD, hDns⟩
          · exact (hsub hD).elim

          · -- Now diffAddDen = 0 and diffAddNum is the vertical numerator.
            rw [hABzero, hD]
            subst x₂
            -- `hy_neg` now identifies y₁ with negY x₁ y₂;
            -- the expression in diffAddNum reduces to the vertical numerator.
            refine SameP1.infty ?_
            simpa [
              XOnly.diffAddRep,
              XOnly.diffAddNum,
              XOnly.diffAddDen,
              XOnly.Δ,
              XOnly.X,
              XOnly.Z,
              WeierstrassCurve.Affine.Point.xRep_zero,
              WeierstrassCurve.Affine.Point.xRep_some,
              WeierstrassCurve.Affine.Point.xRep_neg,
              WeierstrassCurve.b₂,
              WeierstrassCurve.b₄,
              WeierstrassCurve.b₆
            ] using hN

      · -- Main secant case: x₁ ≠ x₂.
        have hnot_vert_plus :
            ¬ (x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
          intro h
          exact hx h.1

        have hnot_vert_minus :
            ¬ (x₁ = x₂ ∧
                y₁ = W.toAffine.negY x₂ (W.toAffine.negY x₂ y₂)) := by
          intro h
          exact hx h.1

        let xp : k :=
          W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)

        let yp : k :=
          W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)

        let xm : k :=
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))

        let ym : k :=
          W.toAffine.addY x₁ x₂ y₁
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))

        have hplus :
            (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
              + Point.some x₂ y₂ h₂ns
            =
            Point.some xp yp
              (by
                dsimp [xp, yp]
                exact W.toAffine.nonsingular_add h₁ns h₂ns hnot_vert_plus) := by
          dsimp [xp, yp]
          exact Point.add_some hnot_vert_plus

        have hneg₂ns :
            W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) := by
          exact (W.toAffine.nonsingular_neg x₂ y₂).2 h₂ns

        have hminus :
            (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
              - Point.some x₂ y₂ h₂ns
            =
            Point.some xm ym
              (by
                dsimp [xm, ym]
                exact W.toAffine.nonsingular_add h₁ns hneg₂ns hnot_vert_minus) := by
          dsimp [xm, ym]
          calc
            (Point.some x₁ y₁ h₁ns : W.toAffine.Point)
                - Point.some x₂ y₂ h₂ns
                =
              Point.some x₁ y₁ h₁ns
                + (-(Point.some x₂ y₂ h₂ns : W.toAffine.Point)) := by
                  simp [sub_eq_add_neg]
            _ =
              Point.some x₁ y₁ h₁ns
                + Point.some x₂ (W.toAffine.negY x₂ y₂) hneg₂ns := by
                  simp [Point.neg_some]
            _ =
              Point.some
                (W.toAffine.addX x₁ x₂
                  (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
                (W.toAffine.addY x₁ x₂ y₁
                  (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
                (by
                  exact W.toAffine.nonsingular_add h₁ns hneg₂ns hnot_vert_minus) := by
                  exact Point.add_some hnot_vert_minus

        have hden : (x₁ - x₂)^2 ≠ 0 := by
          exact sq_ne_zero (sub_ne_zero.mpr hx)

        have hsum :=
          XOnly.addX_sum_mul_sq_of_X_ne
            (W := W) h₁eq h₂eq hx

        have hnum :
            (2 * x₁ * x₂ * (x₁ + x₂)
              + W.b₂ * x₁ * x₂
              + W.b₄ * (x₁ + x₂)
              + W.b₆)
              - xm * (x₁ - x₂)^2
            =
            (x₁ - x₂)^2 * xp := by
          calc
            (2 * x₁ * x₂ * (x₁ + x₂)
                + W.b₂ * x₁ * x₂
                + W.b₄ * (x₁ + x₂)
                + W.b₆)
                - xm * (x₁ - x₂)^2
                =
              (xp + xm) * (x₁ - x₂)^2
                - xm * (x₁ - x₂)^2 := by
                  rw [← hsum]
            _ = (x₁ - x₂)^2 * xp := by
                  ring

        rw [hplus, hminus]
        -- Now both projective representatives are finite:
        -- xRep(A+B) = ![xp,1],
        -- diffAddRep = ![N - xm*(x₁-x₂)^2, (x₁-x₂)^2].
        refine SameP1.affine_of_num_eq hden ?_
        simpa [
          xp,
          xm,
          XOnly.diffAddRep,
          XOnly.diffAddNum,
          XOnly.diffAddDen,
          XOnly.Δ,
          XOnly.X,
          XOnly.Z,
          WeierstrassCurve.Affine.Point.xRep_some,
          WeierstrassCurve.b₂,
          WeierstrassCurve.b₄,
          WeierstrassCurve.b₆
        ] using hnum
```

## 4. Case map

The degenerate cases are exactly these:

| Case | Status | Closing fact |
|---|---:|---|
| `A = 0`, `B = 0` | excluded | `A - B = 0`, contradicts `hsub` |
| `A = 0`, `B ≠ 0` | valid | `A+B=B`, `A-B=-B`, `xRep(-B)=xRep(B)`, `simp` |
| `B = 0`, `A ≠ 0` | valid | `A+B=A`, `A-B=A`, `simp` |
| affine/affine, `x₁ ≠ x₂` | main case | symmetric sum identity + finite projective witness `(x₁-x₂)^2` |
| affine/affine, `x₁ = x₂`, `y₁ = y₂` | excluded | `A=B`, hence `A-B=0` |
| affine/affine, `x₁ = x₂`, `y₁ = negY x₂ y₂` | vertical case | `A+B=0`; `hsub` implies `A` is not 2-torsion; vertical numerator is \((2y+a₁x+a₃)^2\neq0` |

The sum form is definitely better. The direct form for \(x(A+B)\) forces you to carry the \(x(A-B)\) expression through the entire `field_simp`; the symmetric sum identity reduces to one clean `linear_combination 2*h₁ + 2*h₂`.

The projective packaging is:

```lean
-- finite case
SameP1 ![xp, 1] ![num, den]
```

with witness `den : kˣ`, after proving `num = den * xp`.

```lean
-- infinity case
SameP1 ![1, 0] ![num, 0]
```

with witness `num : kˣ`.

That is the whole proof: two algebra helpers, three trivial zero cases, one vertical case, and the main finite witness.
