import FLT.Assumptions.MazurProof.SexticMumford

/-!
# Coefficient extension for balanced Mumford representatives

This is the model-independent coefficient extension for the balanced Mumford
data of a monic sextic.  The only curve-specific datum is the compatibility
of the two sextic equations under the coefficient map.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u v

variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}

/-- Map a balanced Mumford representative along an injective coefficient map
which carries the source sextic equation to the target sextic equation. -/
def Mumford.mapCoeffs (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) : Mumford M' where
  u := D.u.map ι
  v := D.v.map ι
  nInf := D.nInf
  u_monic := D.u_monic.map ι
  deg_u := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.deg_u
  v_reduced := by
    rw [← Polynomial.map_mod ι, D.v_reduced]
  curve_dvd := by
    obtain ⟨q, hq⟩ := D.curve_dvd
    refine ⟨q.map ι, ?_⟩
    calc
      M'.f - (D.v.map ι) ^ 2 = (M.f - D.v ^ 2).map ι := by
        simp [hM]
      _ = (D.u * q).map ι := by rw [hq]
      _ = D.u.map ι * q.map ι := by simp
  infinity_bound := by
    rw [Polynomial.natDegree_map_eq_of_injective hι]
    exact D.infinity_bound

@[simp] theorem mapCoeffs_u
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).u = D.u.map ι := rfl

@[simp] theorem mapCoeffs_v
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).v = D.v.map ι := rfl

@[simp] theorem mapCoeffs_nInf
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (D : Mumford M) :
    (D.mapCoeffs ι hι hM).nInf = D.nInf := rfl

theorem Mumford.mapCoeffs_injective
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) :
    Function.Injective (Mumford.mapCoeffs ι hι hM) := by
  intro D E hDE
  have huMap := congrArg Mumford.u hDE
  have hvMap := congrArg Mumford.v hDE
  have hn := congrArg Mumford.nInf hDE
  have hu : D.u = E.u :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_u] using huMap)
  have hv : D.v = E.v :=
    Polynomial.map_injective ι hι (by simpa only [mapCoeffs_v] using hvMap)
  have hn' : D.nInf = E.nInf := by
    simpa only [mapCoeffs_nInf] using hn
  cases D
  cases E
  simp_all

end

end MazurProof.SexticMumford
