import Mathlib.LinearAlgebra.CrossProduct

/-!
# Unimodular cross products

Two rows in a free rank-three module define a scalar functional by taking
the dot product with their cross product.  When that cross product is
unimodular, the functional is surjective and its kernel is exactly the
span of the two rows.  This is the elementary algebra behind the canonical
generator of a smooth codimension-two complete intersection in affine
three-space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace LinearMap

variable {R : Type*} [CommRing R]

/-- The scalar functional determined by the cross product of two
three-dimensional rows. -/
def crossProductFunctional (a b : Fin 3 → R) : (Fin 3 → R) →ₗ[R] R where
  toFun x := x ⬝ᵥ (a ⨯₃ b)
  map_add' x y := add_dotProduct x y (a ⨯₃ b)
  map_smul' r x := by
    simpa only [smul_eq_mul, RingHom.id_apply] using
      smul_dotProduct r x (a ⨯₃ b)

@[simp]
theorem crossProductFunctional_apply (a b x : Fin 3 → R) :
    crossProductFunctional a b x = x ⬝ᵥ (a ⨯₃ b) :=
  rfl

/-- A unimodular cross product makes its scalar functional surjective. -/
theorem crossProductFunctional_surjective
    {a b s : Fin 3 → R} (hs : s ⬝ᵥ (a ⨯₃ b) = 1) :
    Function.Surjective (crossProductFunctional a b) := by
  intro r
  refine ⟨r • s, ?_⟩
  simp [hs]

/-- If the cross product of two rows is unimodular, its orthogonal
complement is precisely their span. -/
theorem ker_crossProductFunctional
    {a b s : Fin 3 → R} (hs : s ⬝ᵥ (a ⨯₃ b) = 1) :
    LinearMap.ker (crossProductFunctional a b) =
      Submodule.span R (Set.range ![a, b]) := by
  apply le_antisymm
  · intro x hx
    have hxorth : x ⬝ᵥ (a ⨯₃ b) = 0 := by
      simpa only [mem_ker, crossProductFunctional_apply] using hx
    let y := s ⨯₃ x
    have hcross : (a ⨯₃ b) ⨯₃ y = -x := by
      rw [cross_cross_eq_smul_sub_smul']
      rw [dotProduct_comm, hxorth, hs]
      simp
    have hmem : (a ⨯₃ b) ⨯₃ y ∈
        Submodule.span R (Set.range ![a, b]) := by
      rw [cross_cross_eq_smul_sub_smul]
      apply Submodule.sub_mem
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨(1 : Fin 2), by simp⟩
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨(0 : Fin 2), by simp⟩
    rw [hcross] at hmem
    simpa only [neg_mem_iff] using hmem
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simp [crossProductFunctional]
    · simp [crossProductFunctional]

end LinearMap
