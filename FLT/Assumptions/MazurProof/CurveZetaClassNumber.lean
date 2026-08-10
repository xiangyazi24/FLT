import Mathlib

/-!
# The divisor-count proof of the curve class-number formula

For a smooth projective curve over a finite field, let `A n` be the number of
effective divisors of degree `n`.  Its divisor zeta series is

`Z(T) = sum Aₙ Tⁿ`.

Multiplication by `(1-T)(1-qT)` gives coefficients

`pₙ = Aₙ - (q+1)Aₙ₋₁ + qAₙ₋₂`.

The first theorem below proves the exact telescoping identity

`sum_{n=0}^N pₙ = A_N - q A_{N-1}`.

Riemann--Roch supplies the remaining geometric input.  Once
`n >= 2g-1`, each degree-`n` divisor class has a complete linear system with

`1 + q + ... + q^(n-g)`

effective divisors.  Partitioning effective divisors by their degree-zero
Picard class and applying the telescoping identity proves

`P(1) = #Pic^0`.

This module proves that implication rather than taking the class-number
formula as an assumption.  Constructing the effective-divisor family and
proving its Riemann--Roch fibre formula for an actual scheme remain separate
geometric layers.
-/

namespace MazurProof.CurveZetaClassNumber

open Polynomial
open scoped BigOperators

/-! ## Numerator coefficients and telescoping -/

/-- Coefficients obtained by multiplying a divisor-count series
`sum AₙTⁿ` by `(1-T)(1-qT)`.  The first two coefficients are stated
separately so that the sequence is indexed only by natural numbers. -/
def numeratorCoeff (q : ℤ) (A : ℕ → ℤ) : ℕ → ℤ
  | 0 => A 0
  | 1 => A 1 - (q + 1) * A 0
  | n + 2 => A (n + 2) - (q + 1) * A (n + 1) + q * A n

/-- Partial sums of the numerator coefficients telescope to the last two
divisor counts.  This is the algebraic heart of evaluating the numerator at
one. -/
theorem sum_numeratorCoeff (q : ℤ) (A : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), numeratorCoeff q A n =
      A N - q * if N = 0 then 0 else A (N - 1) := by
  induction N with
  | zero => simp [numeratorCoeff]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hN : N = 0
      · subst N
        simp [numeratorCoeff]
        ring
      · have hsucc : N + 1 ≠ 0 := Nat.succ_ne_zero N
        rw [ih]
        simp only [hsucc, hN, if_false]
        cases N with
        | zero => contradiction
        | succ k =>
            simp only [numeratorCoeff]
            simp only [Nat.add_sub_cancel_right]
            ring

/-- The two Riemann--Roch tail values in degrees `2g-1` and `2g` force the
partial numerator to evaluate to the class number `h`.

The hypotheses are denominator-free: multiplying the usual formula
`Aₙ = h(q^(n+1-g)-1)/(q-1)` by `q-1` avoids division in the integer proof. -/
theorem rr_tail_eval
    (q h : ℤ) (A : ℕ → ℤ) (g : ℕ) (hg : 1 ≤ g) (hq : 1 < q)
    (hRR : ∀ n, 2 * g - 1 ≤ n →
      (q - 1) * A n = h * (q ^ (n + 1 - g) - 1)) :
    ∑ n ∈ Finset.range (2 * g + 1), numeratorCoeff q A n = h := by
  rw [sum_numeratorCoeff]
  have h2g_ne : 2 * g ≠ 0 := by omega
  rw [if_neg h2g_ne]
  have htop := hRR (2 * g) (by omega)
  have hprev := hRR (2 * g - 1) (by omega)
  have hexpTop : 2 * g + 1 - g = g + 1 := by omega
  have hexpPrev : (2 * g - 1) + 1 - g = g := by omega
  rw [hexpTop] at htop
  rw [hexpPrev] at hprev
  -- Subtract `q` times the degree `2g-1` formula from the degree `2g` formula.
  have hboundary :
      (q - 1) * (A (2 * g) - q * A (2 * g - 1)) = (q - 1) * h := by
    rw [pow_succ] at htop
    linear_combination htop - q * hprev
  have hqne : q - 1 ≠ 0 := by omega
  exact (mul_left_cancel₀ hqne) hboundary

/-! ## Counting effective divisors by Picard fibres -/

/-- If a map between finite types has constant fibre cardinality `m`, then
the source cardinality is the target cardinality times `m`.

For curves, the map is `DivEff^n -> Pic^0`, translated by a rational base
point, and the fibres are complete linear systems. -/
theorem card_eq_card_mul_fiber
    {Pic Eff : Type*} [Finite Pic] [Finite Eff]
    (f : Eff → Pic) (m : ℕ)
    (hfiber : ∀ c, Nat.card {D : Eff // f D = c} = m) :
    Nat.card Eff = Nat.card Pic * m := by
  classical
  letI := Fintype.ofFinite Pic
  letI := Fintype.ofFinite Eff
  calc
    Nat.card Eff = Nat.card (Σ c, {D : Eff // f D = c}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ c : Pic, Nat.card {D : Eff // f D = c} := Nat.card_sigma
    _ = ∑ _c : Pic, m := by simp only [hfiber]
    _ = Nat.card Pic * m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      simp only [Nat.cast_id]

/-- Cardinality of projective space represented as a geometric sum.  A
complete linear system with `r` independent sections has this cardinality. -/
def linearSystemCard (q r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, q ^ i

/-- Casting the natural-valued projective-space cardinality to the integers
commutes with the finite geometric sum. -/
theorem linearSystemCard_cast (q r : ℕ) :
    (linearSystemCard q r : ℤ) =
      ∑ i ∈ Finset.range r, (q : ℤ) ^ i := by
  simp [linearSystemCard]

/-- Three consecutive projective-space cardinalities satisfy the same
second-order recurrence as the coefficients of `(1-T)(1-qT)`. -/
theorem linearSystemCard_recurrence (q r : ℕ) :
    (linearSystemCard q (r + 2) : ℤ) -
        ((q : ℤ) + 1) * linearSystemCard q (r + 1) +
      (q : ℤ) * linearSystemCard q r = 0 := by
  rw [linearSystemCard_cast, linearSystemCard_cast, linearSystemCard_cast]
  rw [show r + 2 = (r + 1) + 1 by omega, geom_sum_succ,
    geom_sum_succ]
  ring

/-- Riemann--Roch makes every numerator coefficient above degree `2g`
vanish.  Thus the truncation used below is the full numerator, rather than an
arbitrary finite prefix, once the effective-divisor fibre theorem is known. -/
theorem rr_fiber_numeratorCoeff_eq_zero
    {Pic : Type*} [Finite Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (q g : ℕ) (hg : 1 ≤ g)
    (hRRfiber : ∀ n, 2 * g - 1 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard q (n + 1 - g))
    (n : ℕ) (hn : 2 * g + 1 ≤ n) :
    numeratorCoeff (q : ℤ) (fun d => Fintype.card (Effective d)) n = 0 := by
  classical
  letI := Fintype.ofFinite Pic
  have hn0 : 2 * g - 1 ≤ n := by omega
  have hn1 : 2 * g - 1 ≤ n - 1 := by omega
  have hn2 : 2 * g - 1 ≤ n - 2 := by omega
  have hcard (d : ℕ) (hd : 2 * g - 1 ≤ d) :
      Fintype.card (Effective d) =
        Fintype.card Pic * linearSystemCard q (d + 1 - g) := by
    have h := card_eq_card_mul_fiber (classOf d)
      (linearSystemCard q (d + 1 - g)) (hRRfiber d hd)
    simpa only [Nat.card_eq_fintype_card] using h
  have hcard0 := hcard n hn0
  have hcard1 := hcard (n - 1) hn1
  have hcard2 := hcard (n - 2) hn2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
    use n - 2
    omega
  simp only [numeratorCoeff]
  -- Put all three Riemann--Roch dimensions over the same base exponent.
  have hr0 : k + 2 + 1 - g = (k + 2 - 1 - g) + 2 := by omega
  have hr1 : (k + 2 - 1) + 1 - g = (k + 2 - 1 - g) + 1 := by omega
  have hr2 : (k + 2 - 2) + 1 - g = k + 2 - 1 - g := by omega
  rw [hr0] at hcard0
  rw [hr1] at hcard1
  rw [hr2] at hcard2
  have hk1 : k + 2 - 1 = k + 1 := by omega
  have hk2 : k + 2 - 2 = k := by omega
  rw [hk1] at hcard1
  rw [hk2] at hcard2
  rw [hcard0, hcard1, hcard2]
  -- The common Picard cardinal factors out of the geometric-sum recurrence.
  have hrec := linearSystemCard_recurrence q (k + 2 - 1 - g)
  have hr : k + 2 - 1 - g = k + 1 - g := by omega
  rw [hr] at hrec
  push_cast
  linear_combination (Fintype.card Pic : ℤ) * hrec

/-! ## Formal divisor zeta series -/

/-- The formal divisor zeta series with coefficient sequence `A`. -/
noncomputable def divisorZetaSeries (A : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk A

/-- The denominator `(1-T)(1-qT)` of the divisor zeta function. -/
noncomputable def zetaDenominator (q : ℤ) : PowerSeries ℤ :=
  (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)

/-- The zeta denominator has constant coefficient one. -/
theorem zetaDenominator_constantCoeff (q : ℤ) :
    PowerSeries.constantCoeff (zetaDenominator q) = 1 := by
  simp [zetaDenominator]

/-- The formal inverse of the zeta denominator, constructed over the integers
from its unit constant coefficient. -/
noncomputable def zetaDenominatorInverse (q : ℤ) : PowerSeries ℤ :=
  PowerSeries.invOfUnit (zetaDenominator q) 1

/-- The constructed inverse is a right inverse of the denominator. -/
theorem zetaDenominator_mul_inverse (q : ℤ) :
    zetaDenominator q * zetaDenominatorInverse q = 1 := by
  exact PowerSeries.mul_invOfUnit (zetaDenominator q) 1
    (zetaDenominator_constantCoeff q)

/-- Multiplication by the zeta denominator has exactly the coefficient
recurrence recorded by `numeratorCoeff`. -/
theorem coeff_zetaDenominator_mul (q : ℤ) (A : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (zetaDenominator q * divisorZetaSeries A) =
      numeratorCoeff q A n := by
  have hprod :
      zetaDenominator q * divisorZetaSeries A =
        divisorZetaSeries A -
          PowerSeries.C q * (PowerSeries.X * divisorZetaSeries A) -
          PowerSeries.X * divisorZetaSeries A +
          PowerSeries.C q * (PowerSeries.X ^ 2 * divisorZetaSeries A) := by
    simp only [zetaDenominator]
    ring
  rw [hprod]
  cases n with
  | zero =>
      simp [numeratorCoeff, divisorZetaSeries]
  | succ n =>
      cases n with
      | zero =>
          have hzero :
              PowerSeries.coeff 1 (divisorZetaSeries A) = A 1 := by
            simp [divisorZetaSeries]
          have hshiftOne :
              PowerSeries.coeff 1
                (PowerSeries.X * divisorZetaSeries A) = A 0 := by
            simp [divisorZetaSeries]
          have hshiftTwo :
              PowerSeries.coeff 1
                (PowerSeries.X ^ 2 * divisorZetaSeries A) = 0 := by
            rw [PowerSeries.coeff_X_pow_mul']
            norm_num
          simp only [numeratorCoeff, map_add, map_sub,
            PowerSeries.coeff_C_mul]
          rw [hzero, hshiftOne, hshiftTwo]
          ring
      | succ k =>
          simp only [numeratorCoeff, map_add, map_sub,
            PowerSeries.coeff_C_mul]
          have hzero :
              PowerSeries.coeff (k + 2) (divisorZetaSeries A) = A (k + 2) := by
            simp [divisorZetaSeries]
          have hshiftOne :
              PowerSeries.coeff (k + 2)
                (PowerSeries.X * divisorZetaSeries A) = A (k + 1) := by
            simp [divisorZetaSeries]
          have hshiftTwo :
              PowerSeries.coeff (k + 2)
                (PowerSeries.X ^ 2 * divisorZetaSeries A) = A k := by
            simp [divisorZetaSeries]
          rw [hzero, hshiftOne, hshiftTwo]
          ring

/-- Riemann--Roch fibre cardinalities imply that the numerator coefficients
through degree `2g` sum to the cardinality of `Pic^0`.

Unlike `rr_tail_eval`, this statement contains no numerical class-number
parameter.  The class number is derived as `Fintype.card Pic` by partitioning
the actual effective-divisor types into fibres of `classOf`. -/
theorem rr_fiber_eval
    {Pic : Type*} [Fintype Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (q g : ℕ) (hg : 1 ≤ g) (hq : 2 ≤ q)
    (hRRfiber : ∀ n, 2 * g - 1 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard q (n + 1 - g)) :
    ∑ n ∈ Finset.range (2 * g + 1),
        numeratorCoeff (q : ℤ) (fun d => Fintype.card (Effective d)) n =
      Fintype.card Pic := by
  classical
  apply rr_tail_eval (q : ℤ) (Fintype.card Pic)
    (fun d => Fintype.card (Effective d)) g hg (by omega)
  intro n hn
  have hcard := card_eq_card_mul_fiber (classOf n)
    (linearSystemCard q (n + 1 - g)) (hRRfiber n hn)
  have hcard' : Fintype.card (Effective n) =
      Fintype.card Pic * linearSystemCard q (n + 1 - g) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  rw [hcard']
  push_cast
  rw [linearSystemCard_cast]
  calc
    ((q : ℤ) - 1) *
        ((Fintype.card Pic : ℤ) *
          ∑ i ∈ Finset.range (n + 1 - g), (q : ℤ) ^ i) =
      (Fintype.card Pic : ℤ) *
        (((q : ℤ) - 1) *
          ∑ i ∈ Finset.range (n + 1 - g), (q : ℤ) ^ i) := by ring
    _ = (Fintype.card Pic : ℤ) * ((q : ℤ) ^ (n + 1 - g) - 1) := by
      rw [mul_geom_sum]

/-! ## Polynomial form of the class-number formula -/

/-- The degree-`2g` truncation of `(1-T)(1-qT)Z(T)`, formed directly from
the effective-divisor counts. -/
noncomputable def truncatedNumerator (q : ℤ) (A : ℕ → ℤ) (g : ℕ) : ℤ[X] :=
  ∑ n ∈ Finset.range (2 * g + 1), C (numeratorCoeff q A n) * X ^ n

/-- The coefficient of the truncated numerator is the corresponding zeta
coefficient through degree `2g`, and zero afterwards. -/
theorem coeff_truncatedNumerator (q : ℤ) (A : ℕ → ℤ) (g n : ℕ) :
    (truncatedNumerator q A g).coeff n =
      if n < 2 * g + 1 then numeratorCoeff q A n else 0 := by
  classical
  rw [truncatedNumerator, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hn : n < 2 * g + 1
  · rw [if_pos hn]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [Ne.symm hbn]
    · simp [hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by
      intro h
      subst b
      exact hn (Finset.mem_range.mp hb)
    simp [Ne.symm hbn]

/-- Riemann--Roch proves rationality of the divisor zeta series in formal
power-series form: multiplying by `(1-T)(1-qT)` gives the degree-at-most-`2g`
polynomial `truncatedNumerator`.

This removes all high-degree coefficients rather than merely evaluating a
chosen finite truncation. -/
theorem rr_fiber_zeta_rationality
    {Pic : Type*} [Finite Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (q g : ℕ) (hg : 1 ≤ g)
    (hRRfiber : ∀ n, 2 * g - 1 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard q (n + 1 - g)) :
    zetaDenominator q *
        divisorZetaSeries (fun d => Fintype.card (Effective d)) =
      (truncatedNumerator (q : ℤ)
        (fun d => Fintype.card (Effective d)) g : PowerSeries ℤ) := by
  ext n
  rw [coeff_zetaDenominator_mul, Polynomial.coeff_coe,
    coeff_truncatedNumerator]
  by_cases hn : n < 2 * g + 1
  · rw [if_pos hn]
  · rw [if_neg hn]
    exact rr_fiber_numeratorCoeff_eq_zero Effective classOf q g hg hRRfiber n
      (by omega)

/-- Evaluation at one is the sum of the truncated numerator coefficients. -/
theorem truncatedNumerator_eval_one (q : ℤ) (A : ℕ → ℤ) (g : ℕ) :
    (truncatedNumerator q A g).eval 1 =
      ∑ n ∈ Finset.range (2 * g + 1), numeratorCoeff q A n := by
  simp [truncatedNumerator, eval_finsetSum]

/-- Divisor zeta plus the Riemann--Roch fibre theorem gives the curve
class-number identity `P(1)=#Pic^0`.

This is the exact general theorem needed after identifying a concrete curve's
effective-divisor zeta numerator with its point-count numerator. -/
theorem rr_fiber_numerator_eval_one
    {Pic : Type*} [Fintype Pic]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classOf : ∀ n, Effective n → Pic)
    (q g : ℕ) (hg : 1 ≤ g) (hq : 2 ≤ q)
    (hRRfiber : ∀ n, 2 * g - 1 ≤ n → ∀ c,
      Nat.card {D : Effective n // classOf n D = c} =
        linearSystemCard q (n + 1 - g)) :
    (truncatedNumerator (q : ℤ)
      (fun d => Fintype.card (Effective d)) g).eval 1 = Fintype.card Pic := by
  rw [truncatedNumerator_eval_one]
  exact rr_fiber_eval Effective classOf q g hg hq hRRfiber

end MazurProof.CurveZetaClassNumber
