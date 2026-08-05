import FLT.Assumptions.MazurProof.VeluTwoIsogeny

/-!
# The bundled dual map on a standard two-isogeny

The explicit dual formula on

`E' : y² = x(x² - 2ax + a² - 4b)`

lands back on `E : y² = x(x² + ax + b)`.  To prove its additivity without
repeating elliptic-curve group-law algebra, apply the already additive
standard point map once more to `E'`.  Its target is the fourth-power scaling
of `E`; the variable change with scale factor two identifies that curve with
`E`.  Coordinate calculation then identifies the transported homomorphism
with the existing `dualPoint` formula.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.StandardTwoIsogenyDualHom

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.N18RouteC.VariableChangePoints
open MazurProof.VeluTwoIsogeny
open MazurProof.VeluTwoIsogeny.StandardTwoIsogeny

noncomputable section

/-! ## The scaling equivalence after applying the standard map twice -/

/-- Scaling factor two from the twice-quotiented curve back to the original
standard curve. -/
def dualScaleChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (2 : ℚ) (by norm_num)
  r := 0
  s := 0
  t := 0

/-- The inverse scaling constructs the twice-quotiented curve from the
original standard curve. -/
def dualScaleChangeInv : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 0
  s := 0
  t := 0

/-- The raw target obtained by applying `pointMap` to the standard dual. -/
@[reducible] def twiceQuotientCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  curve (-2 * (-2 * a))
    ((-2 * a) ^ 2 - 4 * (a ^ 2 - 4 * b))

/-- Inverse scaling identifies the original curve with the raw twice
quotient. -/
theorem dualScaleChangeInv_curve (a b : ℚ) :
    dualScaleChangeInv • curve a b = twiceQuotientCurve a b := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    norm_num [dualScaleChangeInv, twiceQuotientCurve, curve] <;>
    ring

/-- Forward scaling identifies the raw twice quotient with the original
standard curve. -/
theorem dualScaleChange_curve (a b : ℚ) :
    dualScaleChange • twiceQuotientCurve a b = curve a b := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    norm_num [dualScaleChange, twiceQuotientCurve, curve] <;>
    ring

/-- The raw twice quotient is elliptic because it is a variable-change image
of the original elliptic curve. -/
@[implicit_reducible] noncomputable def twiceQuotientIsElliptic
    (a b : ℚ) [hE : (curve a b).IsElliptic] :
    (twiceQuotientCurve a b).IsElliptic :=
  dualScaleChangeInv_curve a b ▸
    (inferInstance :
      (dualScaleChangeInv • curve a b).IsElliptic)

/-- Additive equivalence from the raw twice quotient back to the original
standard curve. -/
noncomputable def dualScaleEquiv
    (a b : ℚ) [hE : (curve a b).IsElliptic] :
    Point (twiceQuotientCurve a b) ≃+ Point (curve a b) :=
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  (variableChangePointAddEquiv
      (twiceQuotientCurve a b) dualScaleChange).trans
    (curveCastAddEquiv (dualScaleChange_curve a b))

/-! ## Identification with the explicit dual formula -/

/-- Applying the standard forward homomorphism to the standard dual and then
scaling its target produces an additive map back to the source. -/
noncomputable def transportedDualHom
    (a b : ℚ)
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) →+ Point (curve a b) :=
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  (dualScaleEquiv a b).toAddMonoidHom.comp
    { toFun := pointMap
      map_zero' := pointMap_zero
      map_add' := pointMap_add }

/-- The transported additive map agrees pointwise with `dualPoint`. -/
theorem transportedDualHom_apply
    {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (Q : Point (curve (-2 * a) (a ^ 2 - 4 * b))) :
    transportedDualHom a b Q = dualPoint Q := by
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  cases Q with
  | zero =>
      change dualScaleEquiv a b (pointMap 0) = dualPoint 0
      rw [pointMap_zero, map_zero, dualPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hforward :
            pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h) =
              0 := by
          unfold pointMap
          exact dif_pos hx
        have hdual :
            dualPoint (a := a) (b := b) (Point.some x y h) = 0 := by
          unfold dualPoint
          exact dif_pos hx
        change
          dualScaleEquiv a b
              (pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h)) =
            dualPoint (a := a) (b := b) (Point.some x y h)
        rw [hforward, map_zero, hdual]
      · change
          dualScaleEquiv a b
              (pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h)) =
            dualPoint (a := a) (b := b) (Point.some x y h)
        rw [pointMap_some h hx, dualPoint_some h hx]
        unfold dualScaleEquiv
        rw [AddEquiv.trans_apply, variableChangeEquiv_some,
          curveCastAddEquiv_some]
        rw [Point.some.injEq]
        constructor
        · norm_num [variableChangePointX, dualScaleChange, fx, dx]
          ring
        · norm_num [variableChangePointY, dualScaleChange, fy, dy]
          ring

/-- The explicit standard dual formula bundled as an additive
homomorphism. -/
noncomputable def dualPointHom
    (a b : ℚ)
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) →+ Point (curve a b) where
  toFun := dualPoint
  map_zero' := dualPoint_zero
  map_add' P Q := by
    rw [← transportedDualHom_apply (P + Q), map_add,
      transportedDualHom_apply, transportedDualHom_apply]

end

end MazurProof.StandardTwoIsogenyDualHom
