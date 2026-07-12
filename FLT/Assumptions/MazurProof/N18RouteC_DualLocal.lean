import FLT.Assumptions.MazurProof.N18RouteC_DualGlobal
import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSound
import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSolubility
import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeLarge

namespace MazurProof.N18RouteC.DualLocal

open FieldArithmetic Isogeny KummerGeometry
open LocalThree LocalThreeSound GlobalCubes

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

theorem exists_homogeneous_coords
    {u w : L} (hu : u ≠ 0) (hw : w ≠ 0)
    (hcurve : w * (w - 3 * u + 2) = u ^ 3) :
    ∃ U D W : OL,
      U ≠ 0 ∧ D ≠ 0 ∧ W ≠ 0 ∧
      (U : L) = (D : L) ^ 2 * u ∧
      (W : L) = (D : L) ^ 3 * w ∧
      W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3 := by
  obtain ⟨Au, Bu, hBuMem, huFrac⟩ := IsFractionRing.div_surjective OL u
  obtain ⟨Aw, Bw, hBwMem, hwFrac⟩ := IsFractionRing.div_surjective OL w
  have hBu : Bu ≠ 0 := nonZeroDivisors.ne_zero hBuMem
  have hBw : Bw ≠ 0 := nonZeroDivisors.ne_zero hBwMem
  have hAu : Au ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_div] at huFrac
    exact hu huFrac.symm
  have hAw : Aw ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_div] at hwFrac
    exact hw hwFrac.symm
  let D : OL := Bu * Bw
  let U : OL := Au * Bu * Bw ^ 2
  let W : OL := Aw * Bu ^ 3 * Bw ^ 2
  have hD : D ≠ 0 := mul_ne_zero hBu hBw
  have hU : U ≠ 0 := mul_ne_zero (mul_ne_zero hAu hBu) (pow_ne_zero 2 hBw)
  have hW : W ≠ 0 := mul_ne_zero (mul_ne_zero hAw (pow_ne_zero 3 hBu))
    (pow_ne_zero 2 hBw)
  have hUL : (U : L) = (D : L) ^ 2 * u := by
    dsimp [U, D]
    push_cast
    rw [← huFrac]
    field_simp
  have hWL : (W : L) = (D : L) ^ 3 * w := by
    dsimp [W, D]
    push_cast
    rw [← hwFrac]
    field_simp
  refine ⟨U, D, W, hU, hD, hW, hUL, hWL, ?_⟩
  apply Subtype.ext
  change (W : L) * ((W : L) - 3 * (U : L) * (D : L) + 2 * (D : L) ^ 3) =
    (U : L) ^ 3
  rw [hUL, hWL]
  ring_nf at hcurve ⊢
  linear_combination (D : L) ^ 6 * hcurve

theorem piInteger_prime : Prime piInteger := by
  rw [← Ideal.prime_span_singleton_iff,
    ← ThreeAdic.primeAboveThree_eq_span_pi]
  exact ThreeAdic.p3.prime

theorem piInteger_irreducible : Irreducible piInteger :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr piInteger_prime

theorem piInteger_ne_zero : piInteger ≠ 0 := piInteger_prime.ne_zero

theorem qOf_pi_eq_p3 :
    GlobalCubes.qOfIrreducible piInteger piInteger_irreducible = ThreeAdic.p3 := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change Ideal.span ({piInteger} : Set OL) = ThreeAdic.primeAboveThree
  exact ThreeAdic.primeAboveThree_eq_span_pi.symm

theorem ordAt_p3_integral_eq_multiplicity (A : OL) (hA : A ≠ 0) :
    ValuationSupport.ordAt ThreeAdic.p3 (A : L) = multiplicity piInteger A := by
  rw [← qOf_pi_eq_p3]
  exact GlobalCubes.ordAt_algebraMap_eq_multiplicity
    piInteger A piInteger_irreducible hA

theorem exists_weight_primitive
    {U D W : OL} (hU : U ≠ 0) (hD : D ≠ 0) (hW : W ≠ 0)
    (hcurve : W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3) :
    ∃ U' D' W' : OL,
      U' ≠ 0 ∧ D' ≠ 0 ∧ W' ≠ 0 ∧
      W' * (W' - 3 * U' * D' + 2 * D' ^ 3) = U' ^ 3 ∧
      ¬(piInteger ∣ D' ∧ piInteger ^ 2 ∣ U' ∧ piInteger ^ 3 ∣ W') ∧
      ∃ r : ℕ,
        U = piInteger ^ (2 * r) * U' ∧
        D = piInteger ^ r * D' ∧
        W = piInteger ^ (3 * r) * W' := by
  let d := multiplicity piInteger D
  let m := multiplicity piInteger U
  let s := multiplicity piInteger W
  let r := min d (min (m / 2) (s / 3))
  have hrD : r ≤ multiplicity piInteger D := by
    dsimp [r, d]
    omega
  have hrU : 2 * r ≤ multiplicity piInteger U := by
    dsimp [r, m, d, s]
    omega
  have hrW : 3 * r ≤ multiplicity piInteger W := by
    dsimp [r, m, d, s]
    omega
  obtain ⟨D', hDfac⟩ := pow_dvd_of_le_multiplicity hrD
  obtain ⟨U', hUfac⟩ := pow_dvd_of_le_multiplicity hrU
  obtain ⟨W', hWfac⟩ := pow_dvd_of_le_multiplicity hrW
  have hD' : D' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hDfac
    exact hD hDfac
  have hU' : U' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hUfac
    exact hU hUfac
  have hW' : W' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hWfac
    exact hW hWfac
  have hpow2 : piInteger ^ (2 * r) = (piInteger ^ r) ^ 2 := by
    rw [pow_two, ← pow_add]
    congr 1
    omega
  have hpow3 : piInteger ^ (3 * r) = (piInteger ^ r) ^ 3 := by
    rw [pow_succ, pow_two, ← pow_add, ← pow_add]
    congr 1
    omega
  have hcurve' : W' * (W' - 3 * U' * D' + 2 * D' ^ 3) = U' ^ 3 := by
    have hscaled :
        (piInteger ^ r) ^ 6 *
            (W' * (W' - 3 * U' * D' + 2 * D' ^ 3)) =
          (piInteger ^ r) ^ 6 * U' ^ 3 := by
      rw [hpow2] at hUfac
      rw [hpow3] at hWfac
      rw [hUfac, hDfac, hWfac] at hcurve
      linear_combination hcurve
    exact mul_left_cancel₀ (pow_ne_zero 6 (pow_ne_zero r piInteger_ne_zero)) hscaled
  have hprimitive :
      ¬(piInteger ∣ D' ∧ piInteger ^ 2 ∣ U' ∧ piInteger ^ 3 ∣ W') := by
    rintro ⟨hpD, hpU, hpW⟩
    have hfinD : FiniteMultiplicity piInteger D :=
      FiniteMultiplicity.of_prime_left piInteger_prime hD
    have hfinU : FiniteMultiplicity piInteger U :=
      FiniteMultiplicity.of_prime_left piInteger_prime hU
    have hfinW : FiniteMultiplicity piInteger W :=
      FiniteMultiplicity.of_prime_left piInteger_prime hW
    have hrD' : r + 1 ≤ multiplicity piInteger D := by
      apply hfinD.le_multiplicity_of_pow_dvd
      obtain ⟨q, hq⟩ := hpD
      refine ⟨q, ?_⟩
      rw [hDfac, hq, pow_succ]
      ring
    have hrU' : 2 * (r + 1) ≤ multiplicity piInteger U := by
      apply hfinU.le_multiplicity_of_pow_dvd
      obtain ⟨q, hq⟩ := hpU
      refine ⟨q, ?_⟩
      rw [hUfac, hq, ← mul_assoc, ← pow_add]
      congr 2 <;> omega
    have hrW' : 3 * (r + 1) ≤ multiplicity piInteger W := by
      apply hfinW.le_multiplicity_of_pow_dvd
      obtain ⟨q, hq⟩ := hpW
      refine ⟨q, ?_⟩
      rw [hWfac, hq, ← mul_assoc, ← pow_add]
      congr 2 <;> omega
    dsimp [r, d, m, s] at *
    omega
  exact ⟨U', D', W', hU', hD', hW', hcurve', hprimitive,
    r, hUfac, hDfac, hWfac⟩

theorem exact_pi_power_factor {A : OL} (hA : A ≠ 0) :
    ∃ A' : OL,
      A' ≠ 0 ∧ A = piInteger ^ multiplicity piInteger A * A' ∧
      ¬piInteger ∣ A' := by
  obtain ⟨A', hfac⟩ := pow_multiplicity_dvd piInteger A
  have hA' : A' ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfac
    exact hA hfac
  refine ⟨A', hA', hfac, ?_⟩
  intro hp
  have hfin : FiniteMultiplicity piInteger A :=
    FiniteMultiplicity.of_prime_left piInteger_prime hA
  apply hfin.not_pow_dvd_of_multiplicity_lt (lt_add_one _)
  obtain ⟨q, hq⟩ := hp
  refine ⟨q, ?_⟩
  calc
    A = piInteger ^ multiplicity piInteger A * A' := hfac
    _ = piInteger ^ (multiplicity piInteger A + 1) * q := by
      rw [hq, pow_succ, mul_assoc]

theorem primitive_local_shape
    {U D W : OL} (hU : U ≠ 0) (hD : D ≠ 0) (hW : W ≠ 0)
    (hcurve : W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3)
    (hprimitive :
      ¬(piInteger ∣ D ∧ piInteger ^ 2 ∣ U ∧ piInteger ^ 3 ∣ W)) :
    (¬piInteger ∣ W ∧ (¬piInteger ∣ U ∨ ¬piInteger ∣ D)) ∨
    (¬piInteger ∣ D ∧
      ∃ m : ℕ, 0 < m ∧ ∃ U₁ W₁ : OL,
        U₁ ≠ 0 ∧ W₁ ≠ 0 ∧
        ¬piInteger ∣ U₁ ∧ ¬piInteger ∣ W₁ ∧
        U = piInteger ^ m * U₁ ∧ W = piInteger ^ (3 * m) * W₁ ∧
        W₁ * (piInteger ^ (3 * m) * W₁ -
          3 * piInteger ^ m * U₁ * D + 2 * D ^ 3) = U₁ ^ 3) := by
  by_cases hpW : piInteger ∣ W
  · right
    have hpD : ¬piInteger ∣ D := by
      intro hpD
      have hpU : piInteger ∣ U := by
        apply piInteger_prime.dvd_of_dvd_pow
        rw [← hcurve]
        exact dvd_mul_of_dvd_left hpW _
      let m := multiplicity piInteger U
      let d := multiplicity piInteger D
      let s := multiplicity piInteger W
      have hmpos : 0 < m := by
        have : m ≠ 0 := by
          intro hz
          exact (multiplicity_eq_zero.mp (by simpa [m] using hz)) hpU
        omega
      have hdpos : 0 < d := by
        have : d ≠ 0 := by
          intro hz
          exact (multiplicity_eq_zero.mp (by simpa [d] using hz)) hpD
        omega
      have hspos : 0 < s := by
        have : s ≠ 0 := by
          intro hz
          exact (multiplicity_eq_zero.mp (by simpa [s] using hz)) hpW
        omega
      have hsmall : s < 3 ∨ m < 2 := by
        by_contra hnot
        push_neg at hnot
        exact hprimitive ⟨hpD,
          pow_dvd_of_le_multiplicity hnot.2,
          pow_dvd_of_le_multiplicity hnot.1⟩
      let S : OL := W - 3 * U * D + 2 * D ^ 3
      have hS : S ≠ 0 := by
        intro hz
        rw [show W - 3 * U * D + 2 * D ^ 3 = S by rfl, hz, mul_zero] at hcurve
        exact hU ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcurve.symm)
      have h3 : (3 : L) ≠ 0 := by norm_num
      have h2 : (2 : L) ≠ 0 := by norm_num
      have hUL : (U : L) ≠ 0 := by exact_mod_cast hU
      have hDL : (D : L) ≠ 0 := by exact_mod_cast hD
      have hWL : (W : L) ≠ 0 := by exact_mod_cast hW
      have hSL : (S : L) ≠ 0 := by exact_mod_cast hS
      have hordThree :
          ValuationSupport.ordAt ThreeAdic.p3 (3 : L) = 3 :=
        ThreeAdic.ordPi_three
      have hordU : ValuationSupport.ordAt ThreeAdic.p3 (U : L) = m := by
        simpa [m] using ordAt_p3_integral_eq_multiplicity U hU
      have hordD : ValuationSupport.ordAt ThreeAdic.p3 (D : L) = d := by
        simpa [d] using ordAt_p3_integral_eq_multiplicity D hD
      have hordW : ValuationSupport.ordAt ThreeAdic.p3 (W : L) = s := by
        simpa [s] using ordAt_p3_integral_eq_multiplicity W hW
      have hord3UD :
          ValuationSupport.ordAt ThreeAdic.p3 (-((3 : L) * U * D)) = 3 + m + d := by
        rw [ValuationSupport.ordAt_neg,
          ValuationSupport.ordAt_mul ThreeAdic.p3 (mul_ne_zero h3 hUL) hDL,
          ValuationSupport.ordAt_mul ThreeAdic.p3 h3 hUL,
          hordThree, hordU, hordD]
      have hord2D3 :
          ValuationSupport.ordAt ThreeAdic.p3 ((2 : L) * D ^ 3) = 3 * d := by
        rw [ValuationSupport.ordAt_mul ThreeAdic.p3 h2 (pow_ne_zero 3 hDL),
          GlobalCubes.ordAt_two_of_ne_p2 ThreeAdic.p3 GlobalCubes.p2_ne_p3.symm,
          ValuationSupport.ordAt_pow ThreeAdic.p3 hDL 3, hordD]
        norm_num
      have heq : s + ValuationSupport.ordAt ThreeAdic.p3 (S : L) = 3 * m := by
        have hmul := ValuationSupport.ordAt_mul ThreeAdic.p3 hWL hSL
        have hpow := ValuationSupport.ordAt_pow ThreeAdic.p3 hUL 3
        have hcurveL := congrArg (fun z : OL ↦ (z : L)) hcurve
        change (W : L) * (S : L) = (U : L) ^ 3 at hcurveL
        rw [hcurveL] at hmul
        rw [hpow, hordW, hordU] at hmul
        norm_num at hmul ⊢
        exact hmul.symm
      by_cases hslt : s < 3
      · have hs3ud : s < 3 + m + d := by omega
        have hs2d : s < 3 * d := by omega
        have hs3udZ : (s : ℤ) < 3 + (m : ℤ) + d := by exact_mod_cast hs3ud
        have hs2dZ : (s : ℤ) < 3 * (d : ℤ) := by exact_mod_cast hs2d
        have hordS : ValuationSupport.ordAt ThreeAdic.p3 (S : L) = s := by
          have hraw := ValuationSupport.ordAt_sum3_eq_first_of_lt ThreeAdic.p3
            hWL (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h3 hUL) hDL))
            (mul_ne_zero h2 (pow_ne_zero 3 hDL))
            (by simpa [hordW, hord3UD] using hs3udZ)
            (by simpa [hordW, hord2D3] using hs2dZ)
          have hshape :
              (W : L) + (-((3 : L) * (U : L) * (D : L))) +
                  (2 : L) * (D : L) ^ 3 = (S : L) := by
            simp only [S, map_sub, map_add, map_mul, map_pow, map_ofNat]
            ring
          rw [hshape] at hraw
          exact hraw.trans hordW
        rw [hordS] at heq
        omega
      · have hmlt : m < 2 := hsmall.resolve_left hslt
        have hmone : m = 1 := by omega
        have hsge : 3 ≤ s := by omega
        have hordSge : 3 ≤ ValuationSupport.ordAt ThreeAdic.p3 (S : L) := by
          by_cases hsum : (W : L) + (-((3 : L) * U * D)) = 0
          · have hshape : (S : L) = (W : L) + (-((3 : L) * U * D)) +
                (2 : L) * D ^ 3 := by
              simp only [S, map_sub, map_add, map_mul, map_pow, map_ofNat]
              ring
            rw [hshape, hsum, zero_add, hord2D3]
            omega
          · have hge := ValuationSupport.ordAt_sum3_ge_min ThreeAdic.p3
              hWL (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h3 hUL) hDL))
              (mul_ne_zero h2 (pow_ne_zero 3 hDL)) hsum
              (by
                change (W : L) + (-((3 : L) * U * D)) + (2 : L) * D ^ 3 ≠ 0
                have hshape :
                    (W : L) + (-((3 : L) * (U : L) * (D : L))) +
                        (2 : L) * (D : L) ^ 3 = (S : L) := by
                  simp only [S, map_sub, map_add, map_mul, map_pow, map_ofNat]
                  ring
                rw [hshape]
                exact hSL)
            have hshape :
                (W : L) + (-((3 : L) * (U : L) * (D : L))) +
                    (2 : L) * (D : L) ^ 3 = (S : L) := by
              simp only [S, map_sub, map_add, map_mul, map_pow, map_ofNat]
              ring
            rw [hshape] at hge
            rw [hordW, hord3UD, hord2D3] at hge
            have hminNat : min (min s (3 + m + d)) (3 * d) ≥ 3 := by omega
            have hminZ :
                (3 : ℤ) ≤ min (min (s : ℤ) (3 + (m : ℤ) + d)) (3 * (d : ℤ)) := by
              exact_mod_cast hminNat
            exact hminZ.trans hge
        omega
    have hm : 0 < multiplicity piInteger U := by
      have hpU : piInteger ∣ U := by
        apply piInteger_prime.dvd_of_dvd_pow
        rw [← hcurve]
        exact dvd_mul_of_dvd_left hpW _
      have hne : multiplicity piInteger U ≠ 0 := by
        intro hz
        exact (multiplicity_eq_zero.mp hz) hpU
      omega
    let S : OL := W - 3 * U * D + 2 * D ^ 3
    have hS : S ≠ 0 := by
      intro hz
      rw [show W - 3 * U * D + 2 * D ^ 3 = S by rfl, hz, mul_zero] at hcurve
      exact hU ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcurve.symm)
    have hUL : (U : L) ≠ 0 := by exact_mod_cast hU
    have hDL : (D : L) ≠ 0 := by exact_mod_cast hD
    have hWL : (W : L) ≠ 0 := by exact_mod_cast hW
    have hSL : (S : L) ≠ 0 := by exact_mod_cast hS
    have hordThree :
        ValuationSupport.ordAt ThreeAdic.p3 (3 : L) = 3 :=
      ThreeAdic.ordPi_three
    have hordS : ValuationSupport.ordAt ThreeAdic.p3 (S : L) = 0 := by
      have h3UDpos : 0 < ValuationSupport.ordAt ThreeAdic.p3 ((3 : L) * U * D) := by
        rw [ValuationSupport.ordAt_mul ThreeAdic.p3
            (mul_ne_zero (by norm_num) hUL) hDL,
          ValuationSupport.ordAt_mul ThreeAdic.p3 (by norm_num) hUL,
          hordThree,
          ordAt_p3_integral_eq_multiplicity U hU,
          ordAt_p3_integral_eq_multiplicity D hD]
        positivity
      have hWpos : 0 < ValuationSupport.ordAt ThreeAdic.p3 (W : L) := by
        rw [ordAt_p3_integral_eq_multiplicity W hW]
        exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun hz =>
          (multiplicity_eq_zero.mp hz) hpW))
      have h2D : ValuationSupport.ordAt ThreeAdic.p3 ((2 : L) * D ^ 3) = 0 := by
        rw [ValuationSupport.ordAt_mul ThreeAdic.p3 (by norm_num) (pow_ne_zero 3 hDL),
          GlobalCubes.ordAt_two_of_ne_p2 ThreeAdic.p3 GlobalCubes.p2_ne_p3.symm,
          ValuationSupport.ordAt_pow ThreeAdic.p3 hDL 3,
          ordAt_p3_integral_eq_multiplicity D hD]
        have hDmult : multiplicity piInteger D = 0 := multiplicity_eq_zero.mpr hpD
        rw [hDmult]
        norm_num
      have hraw := ValuationSupport.ordAt_sum3_eq_first_of_lt ThreeAdic.p3
        (x := (2 : L) * (D : L) ^ 3) (y := (W : L))
        (z := -((3 : L) * (U : L) * (D : L)))
        (mul_ne_zero (by norm_num) (pow_ne_zero 3 hDL)) hWL
        (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hUL) hDL))
        (by rw [h2D]; exact hWpos)
        (by rw [h2D, ValuationSupport.ordAt_neg]; exact h3UDpos)
      have hshape : (2 : L) * D ^ 3 + (W : L) + (-((3 : L) * U * D)) = (S : L) := by
        simp only [S, map_sub, map_add, map_mul, map_pow, map_ofNat]
        ring
      rw [hshape] at hraw
      simpa [h2D] using hraw
    have hs_eq : multiplicity piInteger W = 3 * multiplicity piInteger U := by
      have hmul := ValuationSupport.ordAt_mul ThreeAdic.p3 hWL hSL
      have hpow := ValuationSupport.ordAt_pow ThreeAdic.p3 hUL 3
      have hcurveL := congrArg (fun z : OL ↦ (z : L)) hcurve
      change (W : L) * (S : L) = (U : L) ^ 3 at hcurveL
      rw [hcurveL] at hmul
      rw [hpow, hordS, ordAt_p3_integral_eq_multiplicity W hW,
        ordAt_p3_integral_eq_multiplicity U hU] at hmul
      norm_num at hmul ⊢
      exact_mod_cast hmul.symm
    obtain ⟨U₁, hU₁, hUfac, hpU₁⟩ := exact_pi_power_factor hU
    obtain ⟨W₁, hW₁, hWfac, hpW₁⟩ := exact_pi_power_factor hW
    refine ⟨hpD, multiplicity piInteger U, hm, U₁, W₁,
      hU₁, hW₁, hpU₁, hpW₁, hUfac, ?_, ?_⟩
    · simpa [hs_eq] using hWfac
    · have hWfac' : W = piInteger ^ (3 * multiplicity piInteger U) * W₁ := by
        simpa [hs_eq] using hWfac
      have hcurveSub :
          (piInteger ^ (3 * multiplicity piInteger U) * W₁) *
              (piInteger ^ (3 * multiplicity piInteger U) * W₁ -
                3 * (piInteger ^ multiplicity piInteger U * U₁) * D + 2 * D ^ 3) =
            (piInteger ^ multiplicity piInteger U * U₁) ^ 3 := by
        calc
          _ = W * (W - 3 * U * D + 2 * D ^ 3) := by
            rw [← hWfac', ← hUfac]
          _ = U ^ 3 := hcurve
          _ = (piInteger ^ multiplicity piInteger U * U₁) ^ 3 := by
            exact congrArg (fun x : OL ↦ x ^ 3) hUfac
      have hscaled :
          piInteger ^ (3 * multiplicity piInteger U) *
            (W₁ * (piInteger ^ (3 * multiplicity piInteger U) * W₁ -
              3 * piInteger ^ multiplicity piInteger U * U₁ * D + 2 * D ^ 3)) =
          piInteger ^ (3 * multiplicity piInteger U) * U₁ ^ 3 := by
        have hpow : (piInteger ^ multiplicity piInteger U) ^ 3 =
            piInteger ^ (3 * multiplicity piInteger U) := by
          rw [← pow_mul]
          congr 1
          omega
        rw [mul_pow, hpow] at hcurveSub
        linear_combination hcurveSub
      exact mul_left_cancel₀
        (pow_ne_zero _ piInteger_ne_zero) hscaled
  · left
    refine ⟨hpW, ?_⟩
    by_contra hnot
    push_neg at hnot
    obtain ⟨hpU, hpD⟩ := hnot
    have hpS : piInteger ∣ W - 3 * U * D + 2 * D ^ 3 := by
      have hpProd : piInteger ∣ U ^ 3 := by
        obtain ⟨q, hq⟩ := hpU
        refine ⟨piInteger ^ 2 * q ^ 3, ?_⟩
        rw [hq]
        ring
      rw [← hcurve] at hpProd
      exact (piInteger_prime.dvd_mul.mp hpProd).resolve_left hpW
    apply hpW
    have h3ud : piInteger ∣ 3 * U * D :=
      dvd_mul_of_dvd_right hpD _
    have h2d : piInteger ∣ 2 * D ^ 3 :=
      dvd_mul_of_dvd_right (dvd_pow hpD (by norm_num)) _
    have hres : piInteger ∣
        (W - 3 * U * D + 2 * D ^ 3) + 3 * U * D - 2 * D ^ 3 :=
      dvd_sub (dvd_add hpS h3ud) h2d
    convert hres using 1 <;> ring

theorem reduceOL_isUnit_of_not_dvd {A : OL}
    (hA : ¬piInteger ∣ A) : IsUnit5 (reduceOL A) := by
  apply reduceOL_isUnit_of_not_mem
  intro hmem
  apply hA
  rw [ThreeAdic.primeAboveThree_eq_span_pi,
    Ideal.mem_span_singleton] at hmem
  exact hmem

theorem reduce_homogeneous
    {U D W : OL}
    (hcurve : W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3) :
    OnHomogeneous (reduceOL U) (reduceOL D) (reduceOL W) := by
  unfold OnHomogeneous
  change reduceOLHom W *
      (reduceOLHom W - 3 * reduceOLHom U * reduceOLHom D +
        2 * reduceOLHom D ^ 3) = reduceOLHom U ^ 3
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat] using
    congrArg reduceOLHom hcurve

set_option maxHeartbeats 2000000 in
theorem reduce_scaled
    {m : ℕ} {U D W : OL}
    (hcurve : W * (piInteger ^ (3 * m) * W -
        3 * piInteger ^ m * U * D + 2 * D ^ 3) = U ^ 3) :
    reduceOL W * (pi5 ^ (3 * m) * reduceOL W -
        3 * pi5 ^ m * reduceOL U * reduceOL D +
          2 * reduceOL D ^ 3) = reduceOL U ^ 3 := by
  change reduceOLHom W *
      (pi5 ^ (3 * m) * reduceOLHom W -
        3 * pi5 ^ m * reduceOLHom U * reduceOLHom D +
          2 * reduceOLHom D ^ 3) = reduceOLHom U ^ 3
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat,
    reduceOLHom_apply, reduceOL_piInteger] using congrArg reduceOLHom hcurve

/-- A primitive homogeneous point has a `pi^(3m)`-normalized Kummer
coordinate whose reduction belongs to the local line generated by `2`. -/
theorem primitive_local_value_in_dual_line
    {U D W : OL} (hU : U ≠ 0) (hD : D ≠ 0) (hW : W ≠ 0)
    (hcurve : W * (W - 3 * U * D + 2 * D ^ 3) = U ^ 3)
    (hprimitive :
      ¬(piInteger ∣ D ∧ piInteger ^ 2 ∣ U ∧ piInteger ^ 3 ∣ W)) :
    ∃ m : ℕ, ∃ W₀ : OL,
      W₀ ≠ 0 ∧ ¬piInteger ∣ W₀ ∧
      W = piInteger ^ (3 * m) * W₀ ∧
      InDualLine (reduceOL W₀) := by
  rcases primitive_local_shape hU hD hW hcurve hprimitive with
      hunit | hpositive
  · rcases hunit with ⟨hpW, hUD⟩
    refine ⟨0, W, hW, hpW, by simp, ?_⟩
    apply homogeneous_unit_value_in_dual_line
      (reduceOL U) (reduceOL D) (reduceOL W)
      (reduceOL_isUnit_of_not_dvd hpW)
    · exact hUD.imp reduceOL_isUnit_of_not_dvd reduceOL_isUnit_of_not_dvd
    · exact reduce_homogeneous hcurve
  · rcases hpositive with
      ⟨hpD, m, hm, U₁, W₁, hU₁, hW₁, hpU₁, hpW₁,
        hUfac, hWfac, hscaled⟩
    refine ⟨m, W₁, hW₁, hpW₁, hWfac, ?_⟩
    have hredU : IsUnit5 (reduceOL U₁) :=
      reduceOL_isUnit_of_not_dvd hpU₁
    have hredD : IsUnit5 (reduceOL D) :=
      reduceOL_isUnit_of_not_dvd hpD
    have hredW : IsUnit5 (reduceOL W₁) :=
      reduceOL_isUnit_of_not_dvd hpW₁
    by_cases hm1 : m = 1
    · subst m
      apply scaled_one_unit_value_in_dual_line
        (reduceOL U₁) (reduceOL D) (reduceOL W₁)
        hredU hredD hredW
      have hr := reduce_scaled hscaled
      simpa [OnScaledOne] using hr
    · have hm2 : 2 ≤ m := by omega
      apply large_scaled_unit_value_in_dual_line
        (reduceOL U₁) (reduceOL D) (reduceOL W₁)
        hredU hredD hredW
      have hr := reduce_scaled hscaled
      have hpow : pi5 ^ (3 * m) = 0 :=
        pi5_pow_eq_zero_of_five_le (by omega)
      have hthree : (3 : R5) * pi5 ^ m = 0 :=
        three_mul_pi5_pow_eq_zero_of_two_le hm2
      rw [hpow, zero_mul, hthree, zero_mul, zero_mul, zero_sub] at hr
      simpa only [neg_zero, zero_add] using hr

end

end MazurProof.N18RouteC.DualLocal
