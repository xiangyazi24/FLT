import FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.AdjoinRoot

/-!
# Quotient bases for arbitrary quadratic N13 special graphs

Evaluation on a generalized Mumford graph identifies its affine quotient
with the monic polynomial quotient by `u`.  When `u` has degree two, the
canonical power basis transports back to the literal quotient basis
`{1,x}`.

Unlike `N13SpecialQuotientBasis`, this construction is parameterized by the
special Mumford graph and does not select a Picard class.
-/

open Module
open Polynomial

namespace MazurProof.N13SpecialGraphQuotientBasis

noncomputable section

abbrev k : Type :=
  N13GoodCoordinateRingTwo.K

abbrev A : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

variable (D : N13GoodCoordinateRingTwo.SemiMumford)

/-- The canonical power basis of the monic quadratic residue algebra. -/
def residueBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) k (AdjoinRoot D.u) :=
  (AdjoinRoot.powerBasis' D.u_monic).basis.reindex
    (finCongr hdeg)

theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis D hdeg i =
      AdjoinRoot.root D.u ^ (i : ℕ) := by
  change
    ((AdjoinRoot.powerBasis' D.u_monic).basis.reindex
        (finCongr hdeg)) i =
      AdjoinRoot.root D.u ^ (i : ℕ)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow,
    finCongr_symm_apply, Fin.val_cast,
    AdjoinRoot.powerBasis'_gen]

@[simp] theorem residueBasis_zero
    (hdeg : D.u.natDegree = 2) :
    residueBasis D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]

/-- Transport graph evaluation to the quotient by the special graph
ideal. -/
def quotientAlgEquiv :
    (A ⧸ N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v) ≃ₐ[k]
      N13GoodCoordinateRingTwo.MumfordResidue D :=
  N13GoodCoordinateRingTwo.mumfordQuotientAlgEquiv D

/-- The transported quadratic power basis on the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) k
      (A ⧸ N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v) :=
  (residueBasis D hdeg).map
    (quotientAlgEquiv D).symm.toLinearEquiv

@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis D hdeg (0 : Fin 2) = 1 := by
  change
    (quotientAlgEquiv D).symm
        (residueBasis D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (quotientAlgEquiv D).symm

@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v)
        (N13GoodCoordinateRingTwo.xClass X) := by
  change
    (quotientAlgEquiv D).symm
        (residueBasis D hdeg 1) =
      Ideal.Quotient.mk
        (N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v)
        (N13GoodCoordinateRingTwo.xClass X)
  rw [residueBasis_one]
  apply (quotientAlgEquiv D).injective
  rw [(quotientAlgEquiv D).apply_symm_apply]
  simp only [quotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      N13GoodCoordinateRingTwo.mumfordEval D
        (N13GoodCoordinateRingTwo.xClass X)
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass]
  rfl

/-- The transported basis family is literally `{1,x}`. -/
theorem coe_quotientBasis
    (hdeg : D.u.natDegree = 2) :
    (quotientBasis D hdeg :
        Fin 2 →
          A ⧸
            N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v) =
      ![1,
        Ideal.Quotient.mk
          (N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v)
          (N13GoodCoordinateRingTwo.xClass X)] := by
  funext i
  fin_cases i <;> simp

end

end MazurProof.N13SpecialGraphQuotientBasis
