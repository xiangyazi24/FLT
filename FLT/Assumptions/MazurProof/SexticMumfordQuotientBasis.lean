import FLT.Assumptions.MazurProof.SexticMumfordIdeal
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.AdjoinRoot

/-!
# The literal basis of a quadratic sextic Mumford quotient

For a monic degree-two Mumford polynomial `u`, graph evaluation identifies
the affine quotient by `(u,Y-v)` with `K[X]/(u)`.  Transporting the canonical
power basis gives the literal quotient basis `{1,x}`.
-/

open Module
open Polynomial

namespace MazurProof.SexticMumfordQuotientBasis

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : SexticMumford.Model K)
variable (D : SexticMumford.SemiMumford M)

/-- The monic polynomial quotient has its canonical quadratic power basis. -/
def residueBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K (AdjoinRoot D.u) :=
  (AdjoinRoot.powerBasis' D.u_monic).basis.reindex
    (finCongr hdeg)

theorem residueBasis_apply
    (hdeg : D.u.natDegree = 2) (i : Fin 2) :
    residueBasis M D hdeg i =
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
    residueBasis M D hdeg (0 : Fin 2) = 1 := by
  simp [residueBasis_apply]

@[simp] theorem residueBasis_one
    (hdeg : D.u.natDegree = 2) :
    residueBasis M D hdeg (1 : Fin 2) =
      AdjoinRoot.root D.u := by
  simp [residueBasis_apply]

/-- Transport the polynomial quotient basis to the affine graph quotient. -/
def quotientBasis
    (hdeg : D.u.natDegree = 2) :
    Basis (Fin 2) K
      (SexticMumford.CoordinateRing M ⧸
        SexticMumford.mumfordIdeal M D.u D.v) :=
  (residueBasis M D hdeg).map
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm.toLinearEquiv

@[simp] theorem quotientBasis_zero
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (0 : Fin 2) = 1 := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 0) = 1
  rw [residueBasis_zero]
  exact map_one (SexticMumford.mumfordQuotientAlgEquiv M D).symm

@[simp] theorem quotientBasis_one
    (hdeg : D.u.natDegree = 2) :
    quotientBasis M D hdeg (1 : Fin 2) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X) := by
  change
    (SexticMumford.mumfordQuotientAlgEquiv M D).symm
        (residueBasis M D hdeg 1) =
      Ideal.Quotient.mk
        (SexticMumford.mumfordIdeal M D.u D.v)
        (SexticMumford.xClass M X)
  rw [residueBasis_one]
  apply (SexticMumford.mumfordQuotientAlgEquiv M D).injective
  rw [(SexticMumford.mumfordQuotientAlgEquiv M D).apply_symm_apply]
  simp only [SexticMumford.mumfordQuotientAlgEquiv]
  change
    AdjoinRoot.root D.u =
      SexticMumford.mumfordEval M D
        (SexticMumford.xClass M X)
  rw [SexticMumford.mumfordEval_xClass]
  rfl

/-- The transported basis family is literally `{1,x}`. -/
theorem coe_quotientBasis
    (hdeg : D.u.natDegree = 2) :
    (quotientBasis M D hdeg :
        Fin 2 →
          SexticMumford.CoordinateRing M ⧸
            SexticMumford.mumfordIdeal M D.u D.v) =
      ![1,
        Ideal.Quotient.mk
          (SexticMumford.mumfordIdeal M D.u D.v)
          (SexticMumford.xClass M X)] := by
  funext i
  fin_cases i <;> simp

end

end MazurProof.SexticMumfordQuotientBasis
