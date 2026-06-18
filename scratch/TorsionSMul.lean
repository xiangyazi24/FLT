import FLT.EllipticCurve.Torsion

universe u
variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable instance test_galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
  smul g P := Point.map (g : K →ₐ[k] K) P
  one_smul P := by
    change Points.map E ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) P = P
    rw [show ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K from rfl]
    simp [Points.map_id]
  mul_smul g h P := by
    change Points.map E ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P =
           Points.map E (g : K →ₐ[k] K) (Points.map E (h : K →ₐ[k] K) P)
    rw [show ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) = (g : K →ₐ[k] K).comp h from rfl]
    have := Points.map_comp E K K K (h : K →ₐ[k] K) (g : K →ₐ[k] K)
    rw [← AddMonoidHom.comp_apply]
    congr 1
    exact this.symm
  smul_zero g := by
    change Points.map E (g : K →ₐ[k] K) 0 = 0
    exact map_zero _
  smul_add g P Q := by
    change Points.map E (g : K →ₐ[k] K) (P + Q) =
           Points.map E (g : K →ₐ[k] K) P + Points.map E (g : K →ₐ[k] K) Q
    exact map_add _ P Q
