import Mathlib.RingTheory.Localization.FractionRing
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectiveProductFormula
private theorem hom_zero_of_regular {R L : Type*} [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (D : Additive Lˣ →+ ℤ)
    (h : ∀ (a : R) (ha : a ≠ 0), D (Additive.ofMul (Units.mk0
      (algebraMap R L a) ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))) = 0)
    (f : Additive Lˣ) : D f = 0 := by
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective R (f.toMul : L)
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [map_zero, zero_div] at heq
    exact (Units.ne_zero f.toMul) heq.symm
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let fa : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L a)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr ha))
  let fb : Additive Lˣ := Additive.ofMul (Units.mk0 (algebraMap R L b)
    ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hb'))
  have hf : f = fa - fb := by
    apply Additive.toMul.injective
    apply Units.ext
    simpa [fa, fb] using heq.symm
  rw [hf, map_sub, h a ha, h b hb', sub_self]


#print axioms hom_zero_of_regular
end MazurProof.N25F_ProjectiveProductFormula
