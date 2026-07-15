import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Prime order 17 exclusion — kernel polynomial infrastructure

For X₀(17), the two noncuspidal rational points P₁=(7,13) and P₂=(11/4,-15/8)
correspond to two oriented rational 17-isogenies:
- P₁ ↔ j₁ = -17·373³/2¹⁷, source E₁ = 14450.o2 = [1,1,0,-660,-7600]
- P₂ ↔ j₂ = -17²·101³/2,   source E₂ = 14450.o1 = [1,1,0,-878710,316677750]

Kernel polynomial k₁ (degree 8, factors as two quartics over ℚ):
  k₁ = (X⁴+30X³+40X²-3200X-12800)(X⁴+200X³+4800X²-166400X-3276800)

Kernel polynomial k₂ (degree 8, irreducible over ℚ):
  k₂ = X⁸-3850X⁷+5336430X⁶-2703764750X⁵-758521052325X⁴
       +1603550459340500X³-801494150624871625X²
       +181027564966569476875X-15893653831170179033125

IMPORTANT: mod 2 fails for k₁ (all coefficients even, k₁≡X⁸ mod 2).
Use mod 3 uniformly: both k₁ and k₂ have no root in 𝔽₃.
-/

open Polynomial

namespace MazurProof.PrimeExclusion17

noncomputable section

/-! ## Fiber 1: quartic factors of k₁ (source 14450.o2) -/

def fiberQ1 : Polynomial ℤ :=
  X ^ 4 + C 30 * X ^ 3 + C 40 * X ^ 2 - C 3200 * X - C 12800

def fiberQ2 : Polynomial ℤ :=
  X ^ 4 + C 200 * X ^ 3 + C 4800 * X ^ 2 - C 166400 * X - C 3276800

theorem fiberQ1_monic : fiberQ1.Monic := by
  unfold fiberQ1; monicity!

theorem fiberQ2_monic : fiberQ2.Monic := by
  unfold fiberQ2; monicity!

theorem fiberQ1_no_root_mod3 (z : ZMod 3) :
    aeval z fiberQ1 ≠ 0 := by
  fin_cases z <;> simp [fiberQ1, aeval_def] <;> decide

theorem fiberQ2_no_root_mod3 (z : ZMod 3) :
    aeval z fiberQ2 ≠ 0 := by
  fin_cases z <;> simp [fiberQ2, aeval_def] <;> decide

theorem fiberQ1_no_rational_root (x : ℚ) :
    aeval x fiberQ1 ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic fiberQ1_monic hx
  have hint : aeval z fiberQ1 = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) fiberQ1 = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 3) z) fiberQ1 = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact fiberQ1_no_root_mod3 _ hmod

theorem fiberQ2_no_rational_root (x : ℚ) :
    aeval x fiberQ2 ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic fiberQ2_monic hx
  have hint : aeval z fiberQ2 = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) fiberQ2 = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 3) z) fiberQ2 = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact fiberQ2_no_root_mod3 _ hmod

/-- k₁ = Q₁ · Q₂ has no rational root. -/
theorem fiber1_no_rational_root (x : ℚ) :
    aeval x (fiberQ1 * fiberQ2) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero (fiberQ1_no_rational_root x) (fiberQ2_no_rational_root x)

/-! ## Fiber 2: irreducible degree-8 polynomial k₂ (source 14450.o1) -/

def fiber2 : Polynomial ℤ :=
  X ^ 8 - C 3850 * X ^ 7 + C 5336430 * X ^ 6
    - C 2703764750 * X ^ 5 - C 758521052325 * X ^ 4
    + C 1603550459340500 * X ^ 3
    - C 801494150624871625 * X ^ 2
    + C 181027564966569476875 * X
    - C 15893653831170179033125

theorem fiber2_monic : fiber2.Monic := by
  unfold fiber2; monicity!

theorem fiber2_no_root_mod3 (z : ZMod 3) :
    aeval z fiber2 ≠ 0 := by
  fin_cases z <;> simp [fiber2, aeval_def] <;> decide

theorem fiber2_no_rational_root (x : ℚ) :
    aeval x fiber2 ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic fiber2_monic hx
  have hint : aeval z fiber2 = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) fiber2 = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 3) z) fiber2 = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact fiber2_no_root_mod3 _ hmod

end

/-! ## Bridge: X₀(17)(ℚ) classification → kernel root

X₀(17) has genus 1 with exactly 4 rational points: 2 cusps + 2 noncuspidal.
The noncuspidal points correspond to two oriented rational 17-isogenies:
  ξ₁ ↔ source 14450.o2, kernel polynomial k₁ = fiberQ1 · fiberQ2
  ξ₂ ↔ source 14450.o1, kernel polynomial k₂ = fiber2

A rational point of order 17 on any E/ℚ gives a rational Y₁(17) point,
whose image in Y₀(17) = X₀(17) \ {cusps} is one of ξ₁ or ξ₂.  The
Y₁ → Y₀ fiber over ξᵢ is the root scheme of κᵢ, so a rational lift
forces κᵢ to have a rational root.

This axiom encapsulates the X₀(17)(ℚ) classification + fiber analysis.
-/

open scoped WeierstrassCurve.Affine in
axiom order17_implies_kernel_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : MazurProof.HasRationalPointOfOrder E 17) :
    (∃ x : ℚ, Polynomial.aeval x (fiberQ1 * fiberQ2) = 0) ∨
    (∃ x : ℚ, Polynomial.aeval x fiber2 = 0)

open scoped WeierstrassCurve.Affine in
theorem no_order_17_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ MazurProof.HasRationalPointOfOrder E 17 := by
  intro h
  rcases order17_implies_kernel_root E h with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact fiber1_no_rational_root x hx
  · exact fiber2_no_rational_root x hx

end MazurProof.PrimeExclusion17
