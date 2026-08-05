import FLT.Assumptions.MazurProof.X017Model
import FLT.Assumptions.MazurProof.StandardTwoIsogenyDualHom

/-!
# The rational two-isogeny pair on the standard `X₀(17)` model

The forward homomorphism transports the general Vélu map through the explicit
source and target changes used by `X017Model`.  The dual homomorphism uses the
bundled standard-coordinate dual formula: it applies the standard isogeny a
second time and scales the twice-quotiented curve back to the source.  The
resulting maps have exactly the types needed by the two-isogeny exact
sequence.

The distinguished point on the target is the transported Vélu kernel point.
Its standard coordinates are `(0,0)`; in particular, it is not the point
`U = (64,0)`, whose dual image is the nonzero source kernel point.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017IsogenySequence

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.StandardTwoIsogenyDualHom

noncomputable section

/-! ## Transported additive homomorphisms -/

/-- The forward rational two-isogeny from the standard source model to its
standard dual. -/
noncomputable def forwardHom : Point standard →+ Point standardDual :=
  (StandardTwoIsogeny.targetEquiv ten_is_root).toAddMonoidHom.comp
    ((veluMapHom ten_is_root).comp ShortToStandard.symm.toAddMonoidHom)

/-- The transported forward homomorphism agrees pointwise with the explicit
standard-coordinate Vélu formula. -/
theorem forwardHom_apply (P : Point standard) :
    forwardHom P = StandardTwoIsogeny.pointMap P := by
  change
    StandardTwoIsogeny.targetEquiv ten_is_root
        (veluMapPoint ten_is_root (ShortToStandard.symm P)) =
      StandardTwoIsogeny.pointMap P
  calc
    _ = StandardTwoIsogeny.pointMap
        (StandardTwoIsogeny.sourceEquiv ten_is_root
          (ShortToStandard.symm P)) :=
      StandardTwoIsogeny.map_conjugacy ten_is_root
        (ShortToStandard.symm P)
    _ = StandardTwoIsogeny.pointMap P := by
      rw [show StandardTwoIsogeny.sourceEquiv ten_is_root =
          ShortToStandard by
        rfl, ShortToStandard.apply_symm_apply]

/-- The order-four point maps to the visible target point `(64,0)`. -/
@[simp] theorem forwardHom_T : forwardHom T = U := by
  rw [forwardHom_apply, pointMap_T]

/-- The visible source two-torsion point is the kernel of the forward
isogeny. -/
@[simp] theorem forwardHom_K : forwardHom K = 0 := by
  rw [forwardHom_apply]
  exact StandardTwoIsogeny.pointMap_kernel

/-- The dual rational two-isogeny from the standard dual back to the standard
source model. -/
noncomputable def dualHom : Point standardDual →+ Point standard :=
  dualPointHom a17 b17

/-- The transported dual homomorphism agrees with the explicit
standard-coordinate dual formula. -/
theorem dualHom_apply (Q : Point standardDual) :
    dualHom Q = StandardTwoIsogeny.dualPoint Q := by
  rfl

/-- The transported dual isogeny composed with the transported forward
isogeny is multiplication by two on the standard source model. -/
theorem dual_comp_forward (P : Point standard) :
    dualHom (forwardHom P) = 2 • P := by
  rw [dualHom_apply, forwardHom_apply,
    StandardTwoIsogeny.dual_comp_pointMap]

/-! ## The correct target-kernel representative -/

/-- The nonzero kernel point of the transported dual isogeny.  Before the
target coordinate change it is the Vélu point `(-20,0)`. -/
noncomputable def eta : Point standardDual :=
  StandardTwoIsogeny.targetEquiv ten_is_root (etaPoint ten_is_root)

/-- In standard target coordinates the dual-kernel representative is the
visible point `(0,0)`. -/
theorem eta_eq_standardDualKernel :
    eta =
      StandardTwoIsogeny.kernelPoint
        (-2 * a17) (a17 ^ 2 - 4 * b17) := by
  change
    StandardTwoIsogeny.targetEquiv ten_is_root
        (Point.some (-2 * (10 : ℚ)) 0
          (eta_nonsingular ten_is_root)) =
      StandardTwoIsogeny.kernelPoint
        (-2 * a17) (a17 ^ 2 - 4 * b17)
  rw [StandardTwoIsogeny.targetEquiv_some]
  unfold StandardTwoIsogeny.kernelPoint
  rw [Point.some.injEq]
  constructor
  · norm_num [StandardTwoIsogeny.targetChange_x]
  · norm_num [StandardTwoIsogeny.targetChange_y]

/-- The target-kernel representative has exact additive order two. -/
theorem eta_order_two : addOrderOf eta = 2 := by
  change
    addOrderOf
        ((StandardTwoIsogeny.targetEquiv ten_is_root).toAddMonoidHom
          (etaPoint ten_is_root)) =
      2
  have h :=
    addOrderOf_injective
      (StandardTwoIsogeny.targetEquiv ten_is_root).toAddMonoidHom
      (StandardTwoIsogeny.targetEquiv ten_is_root).injective
      (etaPoint ten_is_root)
  exact h.trans (etaPoint_order ten_is_root)

/-- The transported dual isogeny kills its distinguished target-kernel
point. -/
@[simp] theorem dualHom_eta : dualHom eta = 0 := by
  rw [dualHom_apply, eta_eq_standardDualKernel]
  rfl

/-- The dual sends the visible target point `(64,0)` to the visible source
kernel point `(0,0)`. -/
@[simp] theorem dualHom_U : dualHom U = K := by
  rw [← forwardHom_T, dual_comp_forward, two_nsmul_T_eq_K]

end

end MazurProof.X017IsogenySequence
