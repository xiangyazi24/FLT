# Q2658 Cyclotomic/PID route audit

Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.

Conclusion: Mathlib has the third-cyclotomic PID/UFD and unit-classification tools, but this route is unlikely to be shorter than the elementary descent for the N=12 residual.  The missing work is not PID/UFD; it is the concrete Eisenstein-integer layer: representing `A^2 + N^2*w`, proving the norm/product formula, proving the two conjugate factors are coprime from `IsCoprime A N`, removing the associated unit, and extracting integer coordinates from a square in the ring of integers.

## Imports and API checks

At this pin, use `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`; the monolithic import `Mathlib.RingTheory.UniqueFactorizationDomain` is not a file.

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

noncomputable section

open scoped NumberField
open NumberField
open IsCyclotomicExtension.Rat.Three

#check IsCyclotomicExtension.Rat.finrank
#check IsCyclotomicExtension.Rat.three_pid
#check IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime
#check IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
#check IsPrimitiveRoot.integralPowerBasisOfPrimePow

#check IsPrimitiveRoot.toInteger
#check IsPrimitiveRoot.coe_toInteger
#check IsPrimitiveRoot.toInteger_isPrimitiveRoot
#check IsPrimitiveRoot.toInteger_cube_eq_one
#check IsCyclotomicExtension.Rat.Three.coe_eta
#check IsCyclotomicExtension.Rat.Three.eta_sq
#check IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one

#check IsCyclotomicExtension.Rat.Three.Units.mem
#check IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent

#check RingOfIntegers.norm
#check RingOfIntegers.coe_norm
#check RingOfIntegers.norm_algebraMap
#check RingOfIntegers.isUnit_norm
#check Algebra.coe_norm_int

#check PrincipalIdealRing.to_uniqueFactorizationMonoid
#check exists_associated_pow_of_mul_eq_pow'
#check exists_associated_pow_of_associated_pow_mul
#check UniqueFactorizationMonoid.factors_mul
#check UniqueFactorizationMonoid.factors_pow
```

Important available theorem shapes:

```lean
-- PID for third cyclotomic ring of integers:
-- IsCyclotomicExtension.Rat.three_pid
--   (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
--     IsPrincipalIdealRing (𝓞 K)

-- Unit list for the third cyclotomic ring of integers:
-- IsCyclotomicExtension.Rat.Three.Units.mem
--   (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ) :
--     u ∈ [1, -1, eta, -eta, eta ^ 2, -eta ^ 2]

-- Unit congruence lemma:
-- IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
--   (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)
--   (hcong : ∃ n : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (u - n : 𝓞 K)) :
--     u = 1 ∨ u = -1

-- Coprime product equal to a power gives one factor associated to a power:
-- exists_associated_pow_of_mul_eq_pow'
--   (hab : IsCoprime a b) (h : a * b = c ^ k) :
--     ∃ d, Associated (d ^ k) a
```

## Minimal representation skeleton

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

noncomputable section

open scoped NumberField
open NumberField
open IsCyclotomicExtension.Rat.Three

section ThirdCyclotomic

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {zeta : K} (hzeta : IsPrimitiveRoot zeta 3)

local notation3 "eta" => (IsPrimitiveRoot.isUnit (hzeta.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "lam" => hzeta.toInteger - 1

def eisensteinAlpha (A N : ℤ) : 𝓞 K :=
  algebraMap ℤ (𝓞 K) (A ^ 2) + algebraMap ℤ (𝓞 K) (N ^ 2) * (eta : 𝓞 K)

def eisensteinAlphaConj (A N : ℤ) : 𝓞 K :=
  algebraMap ℤ (𝓞 K) (A ^ 2) + algebraMap ℤ (𝓞 K) (N ^ 2) * (eta : 𝓞 K) ^ 2

#check (hzeta.toInteger : 𝓞 K)
#check (eta : (𝓞 K)ˣ)
#check (lam : 𝓞 K)
#check (IsCyclotomicExtension.Rat.three_pid K : IsPrincipalIdealRing (𝓞 K))
#check (PrincipalIdealRing.to_uniqueFactorizationMonoid (R := 𝓞 K))
#check (IsCyclotomicExtension.Rat.Three.eta_sq hzeta)
#check (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hzeta)
#check (IsCyclotomicExtension.Rat.Three.Units.mem hzeta (1 : (𝓞 K)ˣ))
#check (IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hzeta)
#check (eisensteinAlpha hzeta (1 : ℤ) (1 : ℤ) : 𝓞 K)
#check (eisensteinAlphaConj hzeta (1 : ℤ) (1 : ℤ) : 𝓞 K)
#check (Algebra.norm ℤ (eisensteinAlpha hzeta (1 : ℤ) (1 : ℤ)) : ℤ)
#check (RingOfIntegers.norm ℚ (eisensteinAlpha hzeta (1 : ℤ) (1 : ℤ)) : 𝓞 ℚ)

end ThirdCyclotomic
```

## Residual theorem statements to isolate if pursuing this route

```lean
-- Product with the formal conjugate.  Prefer proving this before a direct norm theorem.
-- theorem eisensteinAlpha_mul_conj
--     {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
--     {zeta : K} (hzeta : IsPrimitiveRoot zeta 3) (A N : ℤ) :
--     eisensteinAlpha hzeta A N * eisensteinAlphaConj hzeta A N =
--       algebraMap ℤ (𝓞 K) (A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4)

-- The real gate: this is not currently a specialized Mathlib lemma.
-- theorem eisensteinAlpha_coprime_conj
--     {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
--     {zeta : K} (hzeta : IsPrimitiveRoot zeta 3) {A N : ℤ}
--     (hAN : IsCoprime A N) (hN : N ≠ 0) :
--     IsCoprime (eisensteinAlpha hzeta A N) (eisensteinAlphaConj hzeta A N)

-- Then existing UFD extraction applies via `exists_associated_pow_of_mul_eq_pow'`.
-- theorem eisensteinAlpha_associated_square_of_quartic
--     {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
--     {zeta : K} (hzeta : IsPrimitiveRoot zeta 3) {A N S : ℤ}
--     (hcopAB : IsCoprime (eisensteinAlpha hzeta A N) (eisensteinAlphaConj hzeta A N))
--     (hprod : eisensteinAlpha hzeta A N * eisensteinAlphaConj hzeta A N =
--       (algebraMap ℤ (𝓞 K) S) ^ 2) :
--     ∃ gamma : 𝓞 K, Associated (gamma ^ 2) (eisensteinAlpha hzeta A N)
```

## Recommendation

The cyclotomic route is theoretically viable but likely longer here.  Mathlib has the PID, UFD, and unit APIs, but the proof still needs custom lemmas for the product formula, conjugate coprimality, unit removal, and coordinate extraction from `gamma : 𝓞 K` using `IsPrimitiveRoot.integralPowerBasisOfPrimePow`.  The current elementary descent route stays in `ℤ`/`ℕ` and should be less fragile for this repo.
