import FLT.Assumptions.MazurProof.N18RouteC_DualLocal

namespace MazurProof.N18RouteC.LocalCubeComparison

open FieldArithmetic GlobalCubes LocalThree LocalThreeSound DualLocal

noncomputable section

abbrev OL := NumberField.RingOfIntegers L

theorem cubeEq_reduction_of_field_unit_cube
    {X G : OL} (hX : X ≠ 0) (hG : G ≠ 0)
    (hpX : ¬piInteger ∣ X) (hpG : ¬piInteger ∣ G)
    {z : L} (hz : z ≠ 0)
    (hfield : (X : L) = (G : L) * z ^ 3) :
    CubeEq5 (reduceOL X) (reduceOL G) := by
  have hXL : (X : L) ≠ 0 := by exact_mod_cast hX
  have hGL : (G : L) ≠ 0 := by exact_mod_cast hG
  have hordX : ValuationSupport.ordAt ThreeAdic.p3 (X : L) = 0 := by
    rw [DualLocal.ordAt_p3_integral_eq_multiplicity X hX,
      multiplicity_eq_zero.mpr hpX]
    norm_num
  have hordG : ValuationSupport.ordAt ThreeAdic.p3 (G : L) = 0 := by
    rw [DualLocal.ordAt_p3_integral_eq_multiplicity G hG,
      multiplicity_eq_zero.mpr hpG]
    norm_num
  have hordz : ValuationSupport.ordAt ThreeAdic.p3 z = 0 := by
    have hmul := ValuationSupport.ordAt_mul ThreeAdic.p3 hGL (pow_ne_zero 3 hz)
    have hpow := ValuationSupport.ordAt_pow ThreeAdic.p3 hz 3
    rw [← hfield, hordX, hordG, hpow] at hmul
    norm_num at hmul ⊢
    omega
  obtain ⟨A, B, hA, hB, hrel, hzAB⟩ :=
    GlobalCubes.exists_reduced_fraction hz
  have hordFrac := GlobalCubes.ordAt_reduced_fraction_eq hA hB
    DualLocal.piInteger_irreducible
  rw [← hzAB, DualLocal.qOf_pi_eq_p3, hordz] at hordFrac
  have hmultEq : multiplicity piInteger A = multiplicity piInteger B := by
    have hmultEqZ :
        (multiplicity piInteger A : ℤ) = multiplicity piInteger B := by
      omega
    exact_mod_cast hmultEqZ
  have hnotBoth : ¬(piInteger ∣ A ∧ piInteger ∣ B) := by
    rintro ⟨hpA, hpB⟩
    exact DualLocal.piInteger_irreducible.not_isUnit (hrel hpA hpB)
  have hmultA : multiplicity piInteger A = 0 := by
    by_contra hne
    have hpA : piInteger ∣ A := by
      by_contra hnot
      exact hne (multiplicity_eq_zero.mpr hnot)
    have hpB : piInteger ∣ B := by
      by_contra hnot
      have hzB := multiplicity_eq_zero.mpr hnot
      rw [← hmultEq] at hzB
      exact hne hzB
    exact hnotBoth ⟨hpA, hpB⟩
  have hmultB : multiplicity piInteger B = 0 := by rw [← hmultEq, hmultA]
  have hpA : ¬piInteger ∣ A := multiplicity_eq_zero.mp hmultA
  have hpB : ¬piInteger ∣ B := multiplicity_eq_zero.mp hmultB
  have hBL : (B : L) ≠ 0 := by exact_mod_cast hB
  have hcrossL : (X : L) * (B : L) ^ 3 = (G : L) * (A : L) ^ 3 := by
    rw [hzAB] at hfield
    field_simp [hBL] at hfield
    convert hfield using 1 <;> ring
  have hcross : X * B ^ 3 = G * A ^ 3 := by
    apply Subtype.ext
    exact hcrossL
  have hred :
      reduceOL X * reduceOL B ^ 3 = reduceOL G * reduceOL A ^ 3 := by
    have hr := congrArg reduceOLHom hcross
    simpa only [map_mul, map_pow, reduceOLHom_apply] using hr
  have hredA : IsUnit5 (reduceOL A) :=
    DualLocal.reduceOL_isUnit_of_not_dvd hpA
  have hredB : IsUnit5 (reduceOL B) :=
    DualLocal.reduceOL_isUnit_of_not_dvd hpB
  obtain ⟨q, hBq⟩ := exists_right_inverse5 (reduceOL B) hredB
  let r : R5 := reduceOL A * q
  refine ⟨r, isUnit5_mul hredA (isUnit5_of_mul_eq_one _ _ hBq), ?_⟩
  change reduceOL X = reduceOL G * r ^ 3
  calc
    reduceOL X = reduceOL X * (reduceOL B * q) ^ 3 := by rw [hBq]; simp
    _ = (reduceOL X * reduceOL B ^ 3) * q ^ 3 := by ring
    _ = (reduceOL G * reduceOL A ^ 3) * q ^ 3 := by rw [hred]
    _ = reduceOL G * r ^ 3 := by simp [r]; ring

def candidateInteger (i j k : Fin 3) : OL :=
  aInteger ^ i.val * aplusInteger ^ j.val * (2 : OL) ^ k.val

def candidateField (i j k : Fin 3) : L :=
  a ^ i.val * (a + 1) ^ j.val * (2 : L) ^ k.val

theorem candidateInteger_coe (i j k : Fin 3) :
    ((candidateInteger i j k : OL) : L) = candidateField i j k := by
  unfold candidateInteger candidateField
  push_cast
  rfl

theorem candidateInteger_ne_zero (i j k : Fin 3) :
    candidateInteger i j k ≠ 0 := by
  have ha : aInteger ≠ 0 := Units.ne_zero aUnit
  have hap : aplusInteger ≠ 0 := Units.ne_zero aplusUnit
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hap))
    (pow_ne_zero _ (by norm_num))

theorem candidateField_ne_zero (i j k : Fin 3) :
    candidateField i j k ≠ 0 := by
  rw [← candidateInteger_coe]
  exact_mod_cast candidateInteger_ne_zero i j k

theorem candidateInteger_not_dvd_pi (i j k : Fin 3) :
    ¬piInteger ∣ candidateInteger i j k := by
  have ha : ¬piInteger ∣ aInteger := by
    intro h
    have hau : IsUnit aInteger := ⟨aUnit, rfl⟩
    exact DualLocal.piInteger_irreducible.not_isUnit
      (isUnit_iff_dvd_one.mpr <| dvd_trans h (isUnit_iff_dvd_one.mp hau))
  have hap : ¬piInteger ∣ aplusInteger := by
    intro h
    have hapu : IsUnit aplusInteger := ⟨aplusUnit, rfl⟩
    exact DualLocal.piInteger_irreducible.not_isUnit
      (isUnit_iff_dvd_one.mpr <| dvd_trans h (isUnit_iff_dvd_one.mp hapu))
  have htwo : ¬piInteger ∣ (2 : OL) := by
    intro h
    have hmem : (2 : OL) ∈ ThreeAdic.primeAboveThree := by
      rw [ThreeAdic.primeAboveThree_eq_span_pi, Ideal.mem_span_singleton]
      exact h
    exact GlobalCubes.two_not_mem_of_ne_p2 ThreeAdic.p3
      GlobalCubes.p2_ne_p3.symm hmem
  intro hprod
  rcases DualLocal.piInteger_prime.dvd_mul.mp hprod with hleft | hk
  · rcases DualLocal.piInteger_prime.dvd_mul.mp hleft with hi | hj
    · exact ha (DualLocal.piInteger_prime.dvd_of_dvd_pow hi)
    · exact hap (DualLocal.piInteger_prime.dvd_of_dvd_pow hj)
  · exact htwo (DualLocal.piInteger_prime.dvd_of_dvd_pow hk)

theorem reduce_candidateInteger (i j k : Fin 3) :
    reduceOL (candidateInteger i j k) = unitRep i j k := by
  have htwo : reduceOL (2 : OL) = two5 := by
    rw [show (2 : OL) = 1 + 1 by norm_num, reduceOL_add, reduceOL_one]
    rfl
  simp only [candidateInteger, reduceOL_mul, reduceOL_pow,
    reduceOL_aInteger, reduceOL_aplusInteger, htwo]
  unfold unitRep
  rw [pow_eq_ring_pow, pow_eq_ring_pow, pow_eq_ring_pow]
  change a5 ^ i.val * aplus5 ^ j.val * two5 ^ k.val =
    a5 ^ i.val * aplus5 ^ j.val * two5 ^ k.val
  rfl

theorem ordAt_candidateField_p3 (i j k : Fin 3) :
    ValuationSupport.ordAt ThreeAdic.p3 (candidateField i j k) = 0 := by
  have ha : a ≠ 0 := by
    intro hz
    have h := a_mul_inverse
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have hap : a + 1 ≠ 0 := by
    intro hz
    have h := aplus_mul_inverse
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have h2 : (2 : L) ≠ 0 := by norm_num
  have horda : ValuationSupport.ordAt ThreeAdic.p3 a = 0 := by
    simpa using GlobalCubes.ordAt_unit ThreeAdic.p3 aUnit
  have hordap : ValuationSupport.ordAt ThreeAdic.p3 (a + 1) = 0 := by
    simpa using GlobalCubes.ordAt_unit ThreeAdic.p3 aplusUnit
  have hord2 : ValuationSupport.ordAt ThreeAdic.p3 (2 : L) = 0 :=
    GlobalCubes.ordAt_two_of_ne_p2 ThreeAdic.p3 GlobalCubes.p2_ne_p3.symm
  unfold candidateField
  rw [ValuationSupport.ordAt_mul ThreeAdic.p3
      (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hap)) (pow_ne_zero _ h2),
    ValuationSupport.ordAt_mul ThreeAdic.p3
      (pow_ne_zero _ ha) (pow_ne_zero _ hap),
    ValuationSupport.ordAt_pow ThreeAdic.p3 ha,
    ValuationSupport.ordAt_pow ThreeAdic.p3 hap,
    ValuationSupport.ordAt_pow ThreeAdic.p3 h2,
    horda, hordap, hord2]
  norm_num

theorem candidate_pi_exponent_zero
    (i j k l : Fin 3) {x c : L} {m : ℕ} {D W₀ : OL}
    (hx : x ≠ 0) (hc : c ≠ 0) (hD : D ≠ 0) (hW₀ : W₀ ≠ 0)
    (hpW₀ : ¬piInteger ∣ W₀)
    (hlocal : x = pi ^ (3 * m) * (W₀ : L) / (D : L) ^ 3)
    (hglobal : x = candidateField i j k * pi ^ l.val * c ^ 3) :
    l = 0 := by
  have hpi : pi ≠ 0 := by
    intro hz
    have := pi_relation
    rw [hz] at this
    norm_num at this
  have hDL : (D : L) ≠ 0 := by exact_mod_cast hD
  have hW₀L : (W₀ : L) ≠ 0 := by exact_mod_cast hW₀
  have hordpi : ValuationSupport.ordAt ThreeAdic.p3 pi = 1 :=
    ThreeAdic.ordPi_pi
  have hordW₀ : ValuationSupport.ordAt ThreeAdic.p3 (W₀ : L) = 0 := by
    rw [DualLocal.ordAt_p3_integral_eq_multiplicity W₀ hW₀,
      multiplicity_eq_zero.mpr hpW₀]
    norm_num
  have hordLocal :
      ValuationSupport.ordAt ThreeAdic.p3 x =
        3 * (m : ℤ) - 3 * ValuationSupport.ordAt ThreeAdic.p3 (D : L) := by
    rw [hlocal,
      ValuationSupport.ordAt_div ThreeAdic.p3
        (mul_ne_zero (pow_ne_zero _ hpi) hW₀L) (pow_ne_zero _ hDL),
      ValuationSupport.ordAt_mul ThreeAdic.p3 (pow_ne_zero _ hpi) hW₀L,
      ValuationSupport.ordAt_pow ThreeAdic.p3 hpi,
      hordpi, hordW₀,
      ValuationSupport.ordAt_pow ThreeAdic.p3 hDL]
    norm_num
  have hG : candidateField i j k ≠ 0 := candidateField_ne_zero i j k
  have hordGlobal :
      ValuationSupport.ordAt ThreeAdic.p3 x =
        (l.val : ℤ) + 3 * ValuationSupport.ordAt ThreeAdic.p3 c := by
    rw [hglobal,
      ValuationSupport.ordAt_mul ThreeAdic.p3
        (mul_ne_zero hG (pow_ne_zero _ hpi)) (pow_ne_zero _ hc),
      ValuationSupport.ordAt_mul ThreeAdic.p3 hG (pow_ne_zero _ hpi),
      ValuationSupport.ordAt_pow ThreeAdic.p3 hpi,
      ValuationSupport.ordAt_pow ThreeAdic.p3 hc,
      ordAt_candidateField_p3, hordpi]
    norm_num
  have hl : (l.val : ℤ) = 3 *
      ((m : ℤ) - ValuationSupport.ordAt ThreeAdic.p3 (D : L) -
        ValuationSupport.ordAt ThreeAdic.p3 c) := by
    rw [hordGlobal] at hordLocal
    omega
  have hlzero : l.val = 0 := by
    have hlt : l.val < 3 := l.isLt
    omega
  exact Fin.eq_of_val_eq hlzero

theorem inDualLine_of_cubeEq_left {X G : R5}
    (hcube : CubeEq5 X G) (hline : InDualLine X) :
    InDualLine G := by
  obtain ⟨r, hr, hrel⟩ := hcube
  have hrelRing : X = G * r ^ 3 := by
    change X = mul G (r ^ 3)
    rw [← pow_eq_ring_pow]
    exact hrel
  apply inDualLine_unscale G r hr
  rwa [← hrelRing]

/-- The normalized local homogeneous value forces the four global
`S`-unit coordinates to pass the executable `p3` predicate. -/
theorem global_candidate_passes_p3
    (i j k l : Fin 3) {x c : L} {m : ℕ} {D W₀ : OL}
    (hx : x ≠ 0) (hc : c ≠ 0) (hD : D ≠ 0) (hW₀ : W₀ ≠ 0)
    (hpW₀ : ¬piInteger ∣ W₀)
    (hlocal : x = pi ^ (3 * m) * (W₀ : L) / (D : L) ^ 3)
    (hglobal : x = candidateField i j k * pi ^ l.val * c ^ 3)
    (hline : InDualLine (reduceOL W₀)) :
    PassDual3Finite i j k l := by
  have hl : l = 0 := candidate_pi_exponent_zero i j k l hx hc hD hW₀
    hpW₀ hlocal hglobal
  subst l
  refine ⟨rfl, ?_⟩
  have hpi : pi ≠ 0 := by
    intro hz
    have h := pi_relation
    rw [hz] at h
    norm_num at h
  have hDL : (D : L) ≠ 0 := by exact_mod_cast hD
  have hW₀L : (W₀ : L) ≠ 0 := by exact_mod_cast hW₀
  have hG : candidateField i j k ≠ 0 := candidateField_ne_zero i j k
  let z : L := (D : L) * c / pi ^ m
  have hz : z ≠ 0 := div_ne_zero (mul_ne_zero hDL hc) (pow_ne_zero _ hpi)
  have hcombine :
      pi ^ (3 * m) * (W₀ : L) / (D : L) ^ 3 =
        candidateField i j k * c ^ 3 := by
    calc
      _ = x := hlocal.symm
      _ = candidateField i j k * pi ^ (0 : Fin 3).val * c ^ 3 := hglobal
      _ = candidateField i j k * c ^ 3 := by norm_num
  have hWfield :
      (W₀ : L) = ((candidateInteger i j k : OL) : L) * z ^ 3 := by
    rw [candidateInteger_coe]
    dsimp [z]
    have hpow : pi ^ (3 * m) = (pi ^ m) ^ 3 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow] at hcombine
    field_simp [hDL, hpi] at hcombine ⊢
    linear_combination hcombine
  have hcube := cubeEq_reduction_of_field_unit_cube hW₀
    (candidateInteger_ne_zero i j k) hpW₀
    (candidateInteger_not_dvd_pi i j k) hz hWfield
  have hcandidateLine : InDualLine (reduceOL (candidateInteger i j k)) :=
    inDualLine_of_cubeEq_left hcube hline
  rw [reduce_candidateInteger] at hcandidateLine
  exact hcandidateLine

end

end MazurProof.N18RouteC.LocalCubeComparison
