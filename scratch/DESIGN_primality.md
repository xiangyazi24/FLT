# Design: Prime (X₀-X₁) in MvPowerSeries (ChatGPT dm1 Q591)

## Strategy: killCompl + shear

1. Use MvPowerSeries.killCompl to build kill₀ : MvPowerSeries (Fin 2) S →ₐ S⟦X⟧
   - kill₀ sends X₀ ↦ 0, X₁ ↦ T
   - import Mathlib.RingTheory.MvPowerSeries.Rename

2. Key lemma: kill₀ f = 0 ↔ X₀ ∣ f
   - Uses MvPowerSeries.X_dvd_iff

3. Prime X₀: kill₀ maps to domain S⟦X⟧, factor through NoZeroDivisors

4. Transport to Prime (X₀-X₁) via shear automorphism X₀ ↦ X₀-X₁, X₁ ↦ X₁
   - Use substAlgHom or MulEquiv.prime_iff

## Naturality: Mathlib has map_addXYZ (L843-864)

Projective.map_addX, map_addY, map_addZ, map_negAddY are @[simp] lemmas.
Transport chain: formalUCoeff_map → formalU_map → formalW_map → formalPointMv_map → formalAddXYZ_map
