import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Ideal.Over

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Q6822Check

/-! A minimal stand-in for the current FLT infinity-parameter tower. -/

abbrev InfinityParameterRing := Polynomial ℚ
abbrev InfinityChart := ℚ
abbrev infinityChartU : InfinityChart := 0

noncomputable instance infinityChartAlgebra :
    Algebra InfinityParameterRing InfinityChart :=
  (Polynomial.eval₂RingHom (algebraMap ℚ InfinityChart) infinityChartU).toAlgebra

def infinityBoundaryXIdeal : Ideal InfinityChart := ⊥
def infinityBoundaryYIdeal : Ideal InfinityChart := ⊥
def infinityBoundaryZIdeal : Ideal InfinityChart := ⊥

theorem infinityBoundaryXIdeal_isMaximal : infinityBoundaryXIdeal.IsMaximal := by
  simpa [infinityBoundaryXIdeal] using
    (Ideal.bot_isMaximal : (⊥ : Ideal ℚ).IsMaximal)

theorem infinityBoundaryYIdeal_isMaximal : infinityBoundaryYIdeal.IsMaximal := by
  simpa [infinityBoundaryYIdeal] using
    (Ideal.bot_isMaximal : (⊥ : Ideal ℚ).IsMaximal)

theorem infinityBoundaryZIdeal_isMaximal : infinityBoundaryZIdeal.IsMaximal := by
  simpa [infinityBoundaryZIdeal] using
    (Ideal.bot_isMaximal : (⊥ : Ideal ℚ).IsMaximal)

theorem infinityBoundaryXIdeal_isPrime : infinityBoundaryXIdeal.IsPrime :=
  infinityBoundaryXIdeal_isMaximal.isPrime

theorem infinityBoundaryYIdeal_isPrime : infinityBoundaryYIdeal.IsPrime :=
  infinityBoundaryYIdeal_isMaximal.isPrime

theorem infinityBoundaryZIdeal_isPrime : infinityBoundaryZIdeal.IsPrime :=
  infinityBoundaryZIdeal_isMaximal.isPrime

theorem infinityChartU_mem_boundaryX : infinityChartU ∈ infinityBoundaryXIdeal := by
  simp [infinityChartU, infinityBoundaryXIdeal]

theorem infinityChartU_mem_boundaryY : infinityChartU ∈ infinityBoundaryYIdeal := by
  simp [infinityChartU, infinityBoundaryYIdeal]

theorem infinityChartU_mem_boundaryZ : infinityChartU ∈ infinityBoundaryZIdeal := by
  simp [infinityChartU, infinityBoundaryZIdeal]

/-! The proposed FLT implementation starts here. -/

/-- The height-one point `u = 0` on `Spec InfinityParameterRing`. -/
def basePrime :
    IsDedekindDomain.HeightOneSpectrum InfinityParameterRing :=
  Polynomial.idealX ℚ

@[simp] theorem basePrime_asIdeal :
    basePrime.asIdeal =
      Ideal.span ({Polynomial.X} : Set InfinityParameterRing) := by
  rfl

/-- The parameter variable maps to the infinity-chart function `u`. -/
@[simp] theorem infinityParameter_algebraMap_X :
    algebraMap InfinityParameterRing InfinityChart Polynomial.X =
      infinityChartU := by
  change
    (Polynomial.eval₂RingHom (algebraMap ℚ InfinityChart) infinityChartU)
        Polynomial.X =
      infinityChartU
  simp

/-- Any maximal chart ideal containing `u` contracts to `(X)`. -/
private theorem maximal_comap_eq_basePrime
    (P : Ideal InfinityChart)
    (hP : P.IsMaximal)
    (hU : infinityChartU ∈ P) :
    Ideal.comap (algebraMap InfinityParameterRing InfinityChart) P =
      basePrime.asIdeal := by
  symm
  apply Ideal.IsMaximal.eq_of_le
    (basePrime.isPrime.isMaximal basePrime.ne_bot)
    (Ideal.comap_ne_top _ hP.ne_top)
  rw [basePrime_asIdeal, Ideal.span_le]
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst f
  change
    algebraMap InfinityParameterRing InfinityChart Polynomial.X ∈ P
  rw [infinityParameter_algebraMap_X]
  exact hU

@[simp] theorem infinityBoundaryXIdeal_comap :
    Ideal.comap (algebraMap InfinityParameterRing InfinityChart)
        infinityBoundaryXIdeal =
      Ideal.span ({Polynomial.X} : Set InfinityParameterRing) := by
  simpa only [basePrime_asIdeal] using
    maximal_comap_eq_basePrime
      infinityBoundaryXIdeal
      infinityBoundaryXIdeal_isMaximal
      infinityChartU_mem_boundaryX

@[simp] theorem infinityBoundaryYIdeal_comap :
    Ideal.comap (algebraMap InfinityParameterRing InfinityChart)
        infinityBoundaryYIdeal =
      Ideal.span ({Polynomial.X} : Set InfinityParameterRing) := by
  simpa only [basePrime_asIdeal] using
    maximal_comap_eq_basePrime
      infinityBoundaryYIdeal
      infinityBoundaryYIdeal_isMaximal
      infinityChartU_mem_boundaryY

@[simp] theorem infinityBoundaryZIdeal_comap :
    Ideal.comap (algebraMap InfinityParameterRing InfinityChart)
        infinityBoundaryZIdeal =
      Ideal.span ({Polynomial.X} : Set InfinityParameterRing) := by
  simpa only [basePrime_asIdeal] using
    maximal_comap_eq_basePrime
      infinityBoundaryZIdeal
      infinityBoundaryZIdeal_isMaximal
      infinityChartU_mem_boundaryZ

/-- Package a boundary prime together with its contraction equality. -/
private def boundaryPrimeOver
    (P : Ideal InfinityChart)
    (hP : P.IsPrime)
    (hcomap :
      Ideal.comap (algebraMap InfinityParameterRing InfinityChart) P =
        Ideal.span ({Polynomial.X} : Set InfinityParameterRing)) :
    basePrime.asIdeal.primesOver InfinityChart := by
  refine ⟨P, hP, ⟨?_⟩⟩
  change
    basePrime.asIdeal =
      Ideal.comap (algebraMap InfinityParameterRing InfinityChart) P
  rw [basePrime_asIdeal, hcomap]

/-- The boundary point `X` as a prime over `u = 0`. -/
def infinityBoundaryXPrimeOver :
    basePrime.asIdeal.primesOver InfinityChart :=
  boundaryPrimeOver infinityBoundaryXIdeal
    infinityBoundaryXIdeal_isPrime infinityBoundaryXIdeal_comap

/-- The boundary point `Y` as a prime over `u = 0`. -/
def infinityBoundaryYPrimeOver :
    basePrime.asIdeal.primesOver InfinityChart :=
  boundaryPrimeOver infinityBoundaryYIdeal
    infinityBoundaryYIdeal_isPrime infinityBoundaryYIdeal_comap

/-- The boundary point `Z` as a prime over `u = 0`. -/
def infinityBoundaryZPrimeOver :
    basePrime.asIdeal.primesOver InfinityChart :=
  boundaryPrimeOver infinityBoundaryZIdeal
    infinityBoundaryZIdeal_isPrime infinityBoundaryZIdeal_comap

end Q6822Check
