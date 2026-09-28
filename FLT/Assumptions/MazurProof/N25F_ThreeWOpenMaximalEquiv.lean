import FLT.Assumptions.MazurProof.N25F_ThreeWOpenPrimeEquiv
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Maximal ideals on the characteristic-three N25 denominator open

Maximal ideals of the D-localization of the actual W-chart correspond,
by contraction and extension, to maximal ideals of the W-chart quotient
which avoid D.  The correspondence is compatible with the previously
defined prime-ideal correspondence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeWOpenPrimeEquiv

open N25F_ThreeWChartDRegular

/-- Maximal ideals of the actual characteristic-three W-chart which lie
on the denominator open. -/
abbrev WChartMaximalAvoidingDThree :=
  {p : Ideal WChartQuotientThree //
    p.IsMaximal ∧ wChartDenominatorThree ∉ p}

/-- The actual W-chart quotient is Jacobson: it is a quotient of a
finite-variable polynomial ring over the finite field `ZMod 3`. -/
private theorem wChartQuotientThree_isJacobson :
    IsJacobsonRing WChartQuotientThree := by
  infer_instance

/-- Maximal ideals of the D-localization correspond, preserving
inclusion, to maximal ideals of the original W-chart quotient which
avoid D. -/
def wOpenMaximalEquivThree :
    {P : Ideal WChartDLocalizationThree // P.IsMaximal} ≃o
      WChartMaximalAvoidingDThree := by
  letI : IsJacobsonRing WChartQuotientThree :=
    wChartQuotientThree_isJacobson
  exact
    IsLocalization.orderIsoOfMaximal
      (S := WChartDLocalizationThree)
      wChartDenominatorThree

/-- The forward maximal-ideal correspondence is contraction along the
canonical localization map. -/
@[simp]
theorem wOpenMaximalEquivThree_apply_val
    (P : {P : Ideal WChartDLocalizationThree // P.IsMaximal}) :
    (wOpenMaximalEquivThree P).1 =
      P.1.comap
        (algebraMap WChartQuotientThree WChartDLocalizationThree) := by
  rfl

/-- The inverse maximal-ideal correspondence is extension along the
canonical localization map. -/
@[simp]
theorem wOpenMaximalEquivThree_symm_apply_val
    (p : WChartMaximalAvoidingDThree) :
    (wOpenMaximalEquivThree.symm p).1 =
      p.1.map
        (algebraMap WChartQuotientThree WChartDLocalizationThree) := by
  rfl

/-- Forgetting maximality to primality commutes with the W-open
correspondence: both constructions contract an upstairs ideal along the
same localization map. -/
theorem wOpenMaximalEquivThree_commutes_with_contraction
    (P : {P : Ideal WChartDLocalizationThree // P.IsMaximal}) :
    (wOpenMaximalEquivThree P).1 =
      (wOpenPrimeOrderIsoThree
        (⟨P.1, P.2.isPrime⟩ :
          {Q : Ideal WChartDLocalizationThree // Q.IsPrime})).1 := by
  rw [wOpenMaximalEquivThree_apply_val,
    wOpenPrimeOrderIsoThree_apply_val]

end MazurProof.N25F_ThreeWOpenPrimeEquiv
