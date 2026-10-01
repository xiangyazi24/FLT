import FLT.Assumptions.MazurProof.N13SpecialRootJetAgreement

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual Hensel branches at the four finite rational points of the GOOD F2
curve. Their certified nine-jets are the four finite polynomials used in
the bounded principal-function certificate.
-/

namespace MazurProof.N13SpecialFiniteBranchJets

noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate N13SpecialInfinityBranchJets

def hAt (a : K) : K[X] := N13GoodCoordinateRingTwo.hPoly.comp (X + C a)
def rhsAt (a : K) : K[X] := N13GoodCoordinateRingTwo.rhsPoly.comp (X + C a)

theorem hAt_constant (a : K) : (hAt a).coeff 0 = 1 := by
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one a (ZMod.pow_card a) with ha | ha
  · subst a; decide
  · subst a; decide

theorem rhsAt_constant (a : K) : (rhsAt a).coeff 0 = 0 := by
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one a (ZMod.pow_card a) with ha | ha
  · subst a; decide
  · subst a; decide

private theorem beta_constant (p : K[X]) : PowerSeries.constantCoeff (beta p) = p.coeff 0 := by
  rw [beta_eq_coe, ← PowerSeries.coeff_zero_eq_constantCoeff]
  exact Polynomial.coeff_coe p 0

def curvePoly (a : K) : P[X] := X ^ 2 + C (beta (hAt a)) * X - C (beta (rhsAt a))
def xIdeal : Ideal P := Ideal.span ({PowerSeries.X} : Set P)

private instance : IsAdicComplete xIdeal P := by unfold xIdeal; infer_instance

theorem curvePoly_monic (a : K) : (curvePoly a).Monic := by unfold curvePoly; monicity!

theorem exists_root_zero (a : K) :
    ∃ r : P, (curvePoly a).IsRoot r ∧ r ∈ xIdeal := by
  have hrhs : beta (rhsAt a) ∈ xIdeal := by
    apply Ideal.mem_span_singleton.mpr
    apply PowerSeries.X_dvd_iff.mpr
    rw [beta_constant, rhsAt_constant]
  have hzero : (curvePoly a).eval 0 ∈ xIdeal := by
    simpa [curvePoly] using (xIdeal.neg_mem hrhs)
  have hder : (curvePoly a).derivative.eval 0 = beta (hAt a) := by simp [curvePoly]
  have hunit : IsUnit (Ideal.Quotient.mk xIdeal ((curvePoly a).derivative.eval 0)) := by
    rw [hder]
    have hu : IsUnit (beta (hAt a)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, beta_constant, hAt_constant]
      exact isUnit_one
    exact hu.map (Ideal.Quotient.mk xIdeal)
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (curvePoly a) (curvePoly_monic a) 0 hzero hunit
  exact ⟨r, hr, by simpa using hr0⟩

def rootZero (a : K) : P := Classical.choose (exists_root_zero a)
def rootOne (a : K) : P := -beta (hAt a) - rootZero a

theorem rootZero_relation (a : K) :
    rootZero a ^ 2 + beta (hAt a) * rootZero a - beta (rhsAt a) = 0 := by
  simpa [curvePoly] using (Classical.choose_spec (exists_root_zero a)).1

theorem rootZero_constant (a : K) : PowerSeries.constantCoeff (rootZero a) = 0 := by
  apply PowerSeries.X_dvd_iff.mp
  exact Ideal.mem_span_singleton.mp (Classical.choose_spec (exists_root_zero a)).2

theorem rootOne_relation (a : K) :
    rootOne a ^ 2 + beta (hAt a) * rootOne a - beta (rhsAt a) = 0 := by
  unfold rootOne
  linear_combination rootZero_relation a

theorem rootOne_constant (a : K) : PowerSeries.constantCoeff (rootOne a) = 1 := by
  simp only [rootOne, map_sub, map_neg, beta_constant, hAt_constant, rootZero_constant, sub_zero]
  decide

def evalBase (a : K) : K[X] →+* P := Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.X + PowerSeries.C a)

theorem beta_comp (a : K) (p : K[X]) : beta (p.comp (X + C a)) = evalBase a p := by
  simp [beta, evalBase, Polynomial.eval₂_comp]

private theorem affine_root (a : K) (r : P)
    (hr : r ^ 2 + beta (hAt a) * r - beta (rhsAt a) = 0) :
    N13GoodCoordinateRingTwo.curvePoly.eval₂ (evalBase a) r = 0 := by
  simp only [N13GoodCoordinateRingTwo.curvePoly, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  simpa only [hAt, rhsAt, beta_comp] using hr

def branchZero (a : K) : N13GoodCoordinateRingTwo.CoordinateRing →+* P :=
  AdjoinRoot.lift (evalBase a) (rootZero a) (affine_root a _ (rootZero_relation a))

def branchOne (a : K) : N13GoodCoordinateRingTwo.CoordinateRing →+* P :=
  AdjoinRoot.lift (evalBase a) (rootOne a) (affine_root a _ (rootOne_relation a))

@[simp] theorem branchZero_xClass (a : K) (p : K[X]) :
    branchZero a (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := AdjoinRoot.lift_of _

@[simp] theorem branchOne_xClass (a : K) (p : K[X]) :
    branchOne a (N13GoodCoordinateRingTwo.xClass p) = evalBase a p := AdjoinRoot.lift_of _

@[simp] theorem branchZero_yClass (a : K) : branchZero a N13GoodCoordinateRingTwo.yClass = rootZero a :=
  AdjoinRoot.lift_root _

@[simp] theorem branchOne_yClass (a : K) : branchOne a N13GoodCoordinateRingTwo.yClass = rootOne a :=
  AdjoinRoot.lift_root _

theorem zero_zero_jet : (PowerSeries.X : P) ^ 9 ∣ rootZero 0 - beta jetZeroZero := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 0) (rhsAt 0) jetZeroZero _ 9
  · exact hAt_constant _
  · simpa [jetZeroZero] using rootZero_constant (0 : K)
  · exact rootZero_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.1

theorem zero_one_jet : (PowerSeries.X : P) ^ 9 ∣ rootOne 0 - beta jetZeroOne := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 0) (rhsAt 0) jetZeroOne _ 9
  · exact hAt_constant _
  · simpa [jetZeroOne] using rootOne_constant (0 : K)
  · exact rootOne_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.1

theorem one_zero_jet : (PowerSeries.X : P) ^ 9 ∣ rootZero 1 - beta jetOneZero := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 1) (rhsAt 1) jetOneZero _ 9
  · exact hAt_constant _
  · simpa [jetOneZero] using rootZero_constant (1 : K)
  · exact rootZero_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.2.1

theorem one_one_jet : (PowerSeries.X : P) ^ 9 ∣ rootOne 1 - beta jetOneOne := by
  apply N13SpecialRootJetAgreement.root_jet_agreement (hAt 1) (rhsAt 1) jetOneOne _ 9
  · exact hAt_constant _
  · simpa [jetOneOne] using rootOne_constant (1 : K)
  · exact rootOne_relation _
  · simpa [hAt, rhsAt] using jet_polynomials_satisfy_equations.2.2.2.1

end
end MazurProof.N13SpecialFiniteBranchJets
