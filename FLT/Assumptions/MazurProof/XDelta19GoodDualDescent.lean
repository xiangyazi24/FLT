import FLT.Assumptions.MazurProof.XDelta19GoodDescent

/-!
# The complementary Eisenstein descent at level nineteen

The small quotient

`t² = s³ - 3(24s+12)²`

factors over the Eisenstein integers.  Primitive integral coordinates
show that the factor

`n - √(-3) d (24m+12d²)`

is a unit times a cube.  The two nontrivial unit classes are excluded by
finite certificates modulo `27`.  Expanding the remaining cube gives an
explicit preimage under the forward degree-three isogeny.
-/

namespace MazurProof.XDelta19GoodDualDescent

open scoped NumberField

open UniqueFactorizationMonoid
open MazurProof.RationalPointsX135
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny

noncomputable section

local instance goodK3_isCyclotomic :
    IsCyclotomicExtension {3} ℚ N35K3 := by
  change IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ)
  exact CyclotomicField.isCyclotomicExtension 3 ℚ

local instance goodO3_isPrincipalIdealRing :
    IsPrincipalIdealRing N35O3 :=
  IsCyclotomicExtension.Rat.three_pid N35K3

/-! ## Primitive integral quotient coordinates -/

/-- Primitive integral coordinates on the small quotient. -/
theorem quotient_integral_model {s t : ℚ}
    (h : OnQuotient s t) :
    ∃ m n d : ℤ,
      0 < d ∧ Int.gcd m d = 1 ∧
      s = (m : ℚ) / (d : ℚ) ^ 2 ∧
      t = (n : ℚ) / (d : ℚ) ^ 3 ∧
      n ^ 2 = m ^ 3 -
        3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2 := by
  have hcubic : t ^ 2 = s ^ 3 + ((-1728 : ℤ) : ℚ) * s ^ 2 +
      ((-1728 : ℤ) : ℚ) * s + ((-432 : ℤ) : ℚ) := by
    unfold OnQuotient at h
    norm_num at h ⊢
    nlinarith
  obtain ⟨m, d, n, hd, hcop, hs, ht, hmodel⟩ :=
    integral_model_monic_const (-1728) (-1728) (-432) s t hcubic
  refine ⟨m, n, d, hd, hcop, hs, ht, ?_⟩
  linear_combination hmodel

/-- The Eisenstein factor of the primitive quotient equation. -/
noncomputable def dualA (m n d : ℤ) : N35O3 :=
  (n : N35O3) - n35SqrtNegThree *
    (d * (24 * m + 12 * d ^ 2) : ℤ)

/-- Conjugation changes the sign of the square-root term. -/
@[simp] theorem conj_dualA (m n d : ℤ) :
    n35ConjO (dualA m n d) =
      (n : N35O3) + n35SqrtNegThree *
        (d * (24 * m + 12 * d ^ 2) : ℤ) := by
  unfold dualA
  rw [map_sub, map_intCast, map_mul, n35ConjO_sqrtNegThree,
    map_intCast]
  ring

/-- The Eisenstein factor times its conjugate is the cube `m³`. -/
theorem dualA_mul_conj {m n d : ℤ}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    dualA m n d * n35ConjO (dualA m n d) =
      (m : N35O3) ^ 3 := by
  rw [conj_dualA]
  unfold dualA
  have hc := congrArg (fun z : ℤ => (z : N35O3)) hcurve
  push_cast at hc ⊢
  ring_nf
  rw [n35SqrtNegThree_sq]
  linear_combination hc

/-! ## Separation of conjugate prime factors -/

/-- A nonsymmetric irreducible cannot divide a conjugation-stable rational
prime. -/
private theorem nonsymmetric_not_dvd_prime
    {pi r : N35O3} (hpi : Irreducible pi) (hr : Prime r)
    (hrconj : Associated (n35ConjO r) r)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ r := by
  intro hp
  have hpr : Associated pi r :=
    (hpi.dvd_irreducible_iff_associated hr.irreducible).mp hp
  have hcpr : Associated (n35ConjO pi) (n35ConjO r) :=
    hpr.map n35ConjO
  exact hnself (hpr.trans (hcpr.trans hrconj).symm)

/-- A nonsymmetric irreducible cannot divide two in the Eisenstein
integers. -/
private theorem nonsymmetric_not_dvd_two
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ (2 : N35O3) := by
  apply nonsymmetric_not_dvd_prime hpi n35_two_irreducible.prime _ hnself
  have hmap : n35ConjO (2 : N35O3) = 2 := by
    ext
    rw [n35ConjO_coe]
    exact map_ofNat n35ConjK 2
  rw [hmap]

/-- A nonsymmetric irreducible cannot divide the ramified prime above
three. -/
private theorem nonsymmetric_not_dvd_sqrtNegThree
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬pi ∣ n35SqrtNegThree := by
  apply nonsymmetric_not_dvd_prime hpi n35SqrtNegThree_prime _ hnself
  rw [n35ConjO_sqrtNegThree]
  exact Associated.rfl.neg_left

/-- No nonsymmetric irreducible divides both the Eisenstein factor and its
conjugate.  The constant `12` leaves only the excluded primes above two
and three. -/
theorem dualA_no_common_nonsymmetric_factor
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2)
    {pi : N35O3} (hpi : Irreducible pi)
    (hnself : ¬Associated pi (n35ConjO pi)) :
    ¬(pi ∣ dualA m n d ∧ n35ConjO pi ∣ dualA m n d) := by
  rintro ⟨hpA, hpcA⟩
  have hpConjA : pi ∣ n35ConjO (dualA m n d) := by
    have hmapped := map_dvd n35ConjO hpcA
    simpa only [n35ConjO_involutive pi] using hmapped
  have hp2 : ¬pi ∣ (2 : N35O3) :=
    nonsymmetric_not_dvd_two hpi hnself
  have hpq : ¬pi ∣ n35SqrtNegThree :=
    nonsymmetric_not_dvd_sqrtNegThree hpi hnself
  have hpPrime : Prime pi := hpi.prime
  have hp2n : pi ∣ (2 * n : ℤ) := by
    have hs := dvd_add hpA hpConjA
    rw [conj_dualA] at hs
    unfold dualA at hs
    convert hs using 1
    push_cast
    ring
  have hpn : pi ∣ (n : N35O3) := by
    have hsplit :=
      hpPrime.dvd_mul.mp (by simpa only [Int.cast_mul] using hp2n)
    exact hsplit.resolve_left hp2
  have hpMpow : pi ∣ (m : N35O3) ^ 3 := by
    rw [← dualA_mul_conj hcurve]
    exact dvd_mul_of_dvd_left hpA _
  have hpm : pi ∣ (m : N35O3) :=
    hpPrime.dvd_of_dvd_pow hpMpow
  let C : ℤ := d * (24 * m + 12 * d ^ 2)
  have hp2qC :
      pi ∣ (2 : N35O3) * n35SqrtNegThree * (C : N35O3) := by
    have hdif := dvd_sub hpA hpConjA
    rw [conj_dualA] at hdif
    unfold dualA at hdif
    dsimp only [C]
    convert hdif.neg_right using 1
    push_cast
    ring
  have hpqC : pi ∣ n35SqrtNegThree * (C : N35O3) := by
    have hor : pi ∣ (2 : N35O3) ∨
        pi ∣ n35SqrtNegThree * (C : N35O3) :=
      hpPrime.dvd_mul.mp (by simpa [mul_assoc] using hp2qC)
    exact Or.resolve_left hor hp2
  have hpC : pi ∣ (C : N35O3) :=
    (hpPrime.dvd_mul.mp hpqC).resolve_left hpq
  have hpd : ¬pi ∣ (d : N35O3) := by
    intro hpd
    have hcopI : IsCoprime (m : N35O3) (d : N35O3) := by
      have hz : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
      exact hz.map (Int.castRingHom N35O3)
    exact hpi.not_isUnit (hcopI.isUnit_of_dvd' hpm hpd)
  have hpL : pi ∣ (24 * m + 12 * d ^ 2 : ℤ) := by
    have hs : pi ∣ (d : N35O3) *
        (24 * m + 12 * d ^ 2 : ℤ) := by
      simpa [C] using hpC
    exact (hpPrime.dvd_mul.mp hs).resolve_left hpd
  have hp12d2 : pi ∣ (12 : N35O3) * (d : N35O3) ^ 2 := by
    have hs := dvd_sub hpL (dvd_mul_of_dvd_right hpm (24 : N35O3))
    convert hs using 1
    push_cast
    ring
  have hp12 : pi ∣ (12 : N35O3) := by
    rcases hpPrime.dvd_mul.mp hp12d2 with hp12 | hpd2
    · exact hp12
    · exact (hpd (hpPrime.dvd_of_dvd_pow hpd2)).elim
  have hfactor : (12 : N35O3) =
      (2 : N35O3) ^ 2 * (3 : N35O3) := by norm_num
  rw [hfactor] at hp12
  rcases hpPrime.dvd_mul.mp hp12 with hp2sq | hp3
  · exact hp2 (hpPrime.dvd_of_dvd_pow hp2sq)
  · have hpneg3 : pi ∣ -(3 : N35O3) := hp3.neg_right
    have hpq2 : pi ∣ n35SqrtNegThree ^ 2 := by
      rwa [n35SqrtNegThree_sq]
    exact hpq (hpPrime.dvd_of_dvd_pow hpq2)

/-! ## Cube extraction and the unit classes -/

/-- The primitive Eisenstein factor is a unit times a cube. -/
theorem dualA_unit_mul_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    ∃ eps : N35O3ˣ, ∃ B : N35O3,
      dualA m n d = (eps : N35O3) * B ^ 3 := by
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    have hd0 : d ≠ 0 := ne_of_gt hd
    nlinarith [sq_nonneg n, sq_pos_of_ne_zero hd0]
  have hA0 : dualA m n d ≠ 0 := by
    intro hA
    have hp := dualA_mul_conj hcurve
    rw [hA, zero_mul] at hp
    exact (pow_ne_zero 3 (Int.cast_ne_zero.mpr hm0)) hp.symm
  apply n35_unit_mul_cube_of_mul_conj_cube n35ConjO
    n35ConjO_involutive hA0 (dualA_mul_conj hcurve)
  intro pi hpi
  by_cases hs : Associated pi (n35ConjO pi)
  · exact Or.inl hs
  · exact Or.inr
      (dualA_no_common_nonsymmetric_factor hcop hcurve hpi hs)

/-- Modulo cubes, only the three powers of the Eisenstein root of unity
can occur. -/
theorem dualA_three_cubeclasses
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    (∃ B : N35O3, dualA m n d = B ^ 3) ∨
      (∃ B : N35O3,
        dualA m n d = n35ZetaUnit * B ^ 3) ∨
      (∃ B : N35O3,
        dualA m n d = n35ZetaUnit ^ 2 * B ^ 3) := by
  obtain ⟨eps, B, hA⟩ := dualA_unit_mul_cube hd hcop hcurve
  rcases n35K3_unit_mod_cube eps with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; left
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring
  · right; right
    refine ⟨(v : N35O3) * B, ?_⟩
    rw [hA, hv]
    push_cast
    ring

/-- Taking norms of a unit-times-cube identity recovers the primitive
horizontal numerator as an Eisenstein norm. -/
theorem m_eq_coord_norm_of_unit_cube
    {m n d a b : ℤ} {u : N35O3}
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2)
    (hu : u * n35ConjO u = 1)
    (hclass : dualA m n d =
      u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) :
    m = n35NormForm a b := by
  have heqO : (m : N35O3) ^ 3 =
      (n35NormForm a b : N35O3) ^ 3 := by
    calc
      (m : N35O3) ^ 3 =
          dualA m n d * n35ConjO (dualA m n d) :=
        (dualA_mul_conj hcurve).symm
      _ = (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
          n35ConjO
            (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) := by
        rw [hclass]
      _ = (n35NormForm a b : N35O3) ^ 3 := by
        rw [map_mul, map_pow]
        rw [show
          (u * ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) *
              (n35ConjO u *
                n35ConjO
                  ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3) =
            (u * n35ConjO u) *
              (((a : N35O3) + (b : N35O3) * n35Omega) *
                n35ConjO
                  ((a : N35O3) + (b : N35O3) * n35Omega)) ^ 3 by ring,
          hu, one_mul, n35_coord_mul_conj]
  have heqZ : m ^ 3 = n35NormForm a b ^ 3 := by
    exact_mod_cast heqO
  exact (show Odd 3 by decide).pow_injective heqZ

/-! ## Finite exclusion of the two nontrivial unit classes -/

/-- The first homogeneous covering form attached to a nontrivial unit
class. -/
def coverRho (X Y Z : ℤ) : ℤ :=
  X ^ 3 - 3 * Y ^ 3 + 24 * Z ^ 3 + 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z

/-- The conjugate homogeneous covering form. -/
def coverRhoSq (X Y Z : ℤ) : ℤ :=
  X ^ 3 + 3 * Y ^ 3 + 24 * Z ^ 3 - 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Every zero of the first covering form modulo `27` is divisible by
three in all coordinates. -/
private theorem coverRho_mod_twentySeven :
    ∀ X Y Z : ZMod 27,
      X ^ 3 - 3 * Y ^ 3 + 24 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Every zero of the conjugate covering form modulo `27` is divisible
by three in all coordinates. -/
private theorem coverRhoSq_mod_twentySeven :
    ∀ X Y Z : ZMod 27,
      X ^ 3 + 3 * Y ^ 3 + 24 * Z ^ 3 - 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by
  decide

/-- An integral zero of the first covering form has every coordinate
divisible by three. -/
theorem coverRho_all_three_dvd {X Y Z : ℤ}
    (h : coverRho X Y Z = 0) :
    3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have h27 := congrArg (fun z : ℤ => (z : ZMod 27)) h
  unfold coverRho at h27
  push_cast at h27
  have hc := coverRho_mod_twentySeven (X : ZMod 27)
    (Y : ZMod 27) (Z : ZMod 27) h27
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 3).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Z 3).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- An integral zero of the conjugate covering form has every coordinate
divisible by three. -/
theorem coverRhoSq_all_three_dvd {X Y Z : ℤ}
    (h : coverRhoSq X Y Z = 0) :
    3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have h27 := congrArg (fun z : ℤ => (z : ZMod 27)) h
  unfold coverRhoSq at h27
  push_cast at h27
  have hc := coverRhoSq_mod_twentySeven (X : ZMod 27)
    (Y : ZMod 27) (Z : ZMod 27) h27
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd X 3).mp
    simpa [ZMod.castHom_apply] using hc.1
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp
    simpa [ZMod.castHom_apply] using hc.2.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Z 3).mp
    simpa [ZMod.castHom_apply] using hc.2.2

/-- Common divisibility by three contradicts the primitive denominator
normalization. -/
private theorem common_three_contradiction {m d a b : ℤ}
    (hcop : Int.gcd m d = 1) (hm : m = n35NormForm a b)
    (h3x : (3 : ℤ) ∣ 2 * a - b) (h3b : (3 : ℤ) ∣ b)
    (h3z : (3 : ℤ) ∣ 2 * d) :
    False := by
  have h32a : (3 : ℤ) ∣ 2 * a := by
    simpa [sub_eq_add_neg, add_assoc] using dvd_add h3x h3b
  have h3a : (3 : ℤ) ∣ a := by
    have hor : (3 : ℤ) ∣ 2 ∨ (3 : ℤ) ∣ a :=
      (by norm_num : Prime (3 : ℤ)).dvd_mul.mp h32a
    exact Or.resolve_left hor (by norm_num)
  have h3d : (3 : ℤ) ∣ d := by
    have hor : (3 : ℤ) ∣ 2 ∨ (3 : ℤ) ∣ d :=
      (by norm_num : Prime (3 : ℤ)).dvd_mul.mp h3z
    exact Or.resolve_left hor (by norm_num)
  obtain ⟨ka, hka⟩ := h3a
  obtain ⟨kb, hkb⟩ := h3b
  have h3m : (3 : ℤ) ∣ m := by
    refine ⟨3 * (ka ^ 2 - ka * kb + kb ^ 2), ?_⟩
    rw [hm, hka, hkb]
    unfold n35NormForm
    ring
  have hcopI : IsCoprime m d := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hu : IsUnit (3 : ℤ) := hcopI.isUnit_of_dvd' h3m h3d
  rw [Int.isUnit_iff_abs_eq] at hu
  norm_num at hu

/-- The unit class `ζ` has no primitive solution. -/
theorem dualA_not_zeta_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : dualA m n d = (n35ZetaUnit : N35O3) * B ^ 3) :
    False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : dualA m n d = (n35ZetaUnit : N35O3) *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_norm_one hclass'
  let C : ℤ := d * (24 * m + 12 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((-I : ℤ) : N35O3) +
          ((R - I : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) +
          ((-2 * C : ℤ) : N35O3) * n35Omega =
          dualA m n d := by
        unfold dualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((-I : ℤ) : N35O3) +
          ((R - I : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs]
        ring
  have hcoeff : -2 * C = R - I := (n35_coords_injective hcoords).2
  have hG : coverRhoSq (2 * a - b) b (2 * d) = 0 := by
    dsimp [C, R, I] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold coverRhoSq
    linear_combination -8 * hcoeff
  obtain ⟨h3x, h3b, h3z⟩ := coverRhoSq_all_three_dvd hG
  exact common_three_contradiction hcop hm h3x h3b h3z

/-- The unit class `ζ²` has no primitive solution. -/
theorem dualA_not_zeta_sq_cube
    {m n d : ℤ} (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2)
    {B : N35O3}
    (hclass : dualA m n d =
      (n35ZetaUnit : N35O3) ^ 2 * B ^ 3) :
    False := by
  obtain ⟨a, b, hB⟩ := n35O3_exists_coords B
  have hclass' : dualA m n d = (n35ZetaUnit : N35O3) ^ 2 *
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hB] using hclass
  have hm := m_eq_coord_norm_of_unit_cube hcurve
    n35ZetaUnit_sq_norm_one hclass'
  let C : ℤ := d * (24 * m + 12 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        ((I - R : ℤ) : N35O3) + ((-R : ℤ) : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) +
          ((-2 * C : ℤ) : N35O3) * n35Omega =
          dualA m n d := by
        unfold dualA n35SqrtNegThree C
        push_cast
        ring
      _ = (n35ZetaUnit : N35O3) ^ 2 *
          ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass'
      _ = ((I - R : ℤ) : N35O3) +
          ((-R : ℤ) : N35O3) * n35Omega := by
        rw [n35_coord_cube, n35ZetaUnit_val]
        have hs : n35Omega ^ 2 = -n35Omega - 1 := by
          linear_combination n35Omega_relation
        unfold R I
        push_cast
        ring_nf
        rw [hs, n35Omega_cube]
        ring
  have hcoeff : -2 * C = -R := (n35_coords_injective hcoords).2
  have hG : coverRho (-(2 * a - b)) (-b) (2 * d) = 0 := by
    dsimp [C, R] at hcoeff
    rw [hm] at hcoeff
    unfold n35NormForm at hcoeff
    unfold coverRho
    linear_combination -8 * hcoeff
  obtain ⟨h3xneg, h3bneg, h3z⟩ := coverRho_all_three_dvd hG
  have h3x : (3 : ℤ) ∣ 2 * a - b := by
    simpa only [dvd_neg] using h3xneg
  have h3b : (3 : ℤ) ∣ b := by
    simpa only [dvd_neg] using h3bneg
  exact common_three_contradiction hcop hm h3x h3b h3z

/-- The primitive Eisenstein factor is an actual cube. -/
theorem dualA_is_cube
    {m n d : ℤ} (hd : 0 < d) (hcop : Int.gcd m d = 1)
    (hcurve : n ^ 2 = m ^ 3 -
      3 * d ^ 2 * (24 * m + 12 * d ^ 2) ^ 2) :
    ∃ B : N35O3, dualA m n d = B ^ 3 := by
  rcases dualA_three_cubeclasses hd hcop hcurve with h | h | h
  · exact h
  · obtain ⟨B, hB⟩ := h
    exact (dualA_not_zeta_cube hcop hcurve hB).elim
  · obtain ⟨B, hB⟩ := h
    exact (dualA_not_zeta_sq_cube hcop hcurve hB).elim

/-! ## Explicit recovery of a preimage -/

/-- The recovered cubic-cover coordinates lie on the good model. -/
private theorem inverse_good_identity {u v : ℚ} (hv : v + 8 ≠ 0)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (u * (-228 / (v + 8)) / 3) ^ 2 =
      (-228 / (v + 8)) ^ 3 +
        (8 * (-228 / (v + 8)) + 76) ^ 2 := by
  field_simp [hv]
  linear_combination 51984 * hrel

/-- The recovered point has the prescribed forward horizontal
coordinate. -/
private theorem inverse_x_identity {u v s : ℚ} (hv : v + 8 ≠ 0)
    (hs : s = u ^ 2 + 3 * v ^ 2)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (9 * (-228 / (v + 8)) ^ 3 +
        768 * (-228 / (v + 8)) ^ 2 +
        21888 * (-228 / (v + 8)) + 207936) /
      (-228 / (v + 8)) ^ 2 = s := by
  rw [hs]
  field_simp [hv]
  linear_combination (-51984) * hrel

/-- The recovered point has the prescribed forward vertical
coordinate. -/
private theorem inverse_y_identity {u v t : ℚ} (hv : v + 8 ≠ 0)
    (ht : t = u ^ 3 - 9 * u * v ^ 2)
    (hrel : u ^ 2 * v + 8 * u ^ 2 - v ^ 3 +
      24 * v ^ 2 + 4 = 0) :
    (27 * (-228 / (v + 8)) ^ 3 *
          (u * (-228 / (v + 8)) / 3) -
        65664 * (-228 / (v + 8)) *
          (u * (-228 / (v + 8)) / 3) -
        1247616 * (u * (-228 / (v + 8)) / 3)) /
      (-228 / (v + 8)) ^ 3 = t := by
  rw [ht]
  field_simp [hv]
  linear_combination (-155952 * u) * hrel

/-- Every affine rational point on the small quotient has an explicit
preimage under the forward degree-three isogeny. -/
theorem quotient_affine_has_threeIsogeny_preimage {s t : ℚ}
    (hquotient : OnQuotient s t) :
    ∃ x y : ℚ, x ≠ 0 ∧ OnGood x y ∧
      threeIsogenyX x = s ∧ threeIsogenyY x y = t := by
  obtain ⟨m, n, d, hd, hcop, hs, ht, hcurve⟩ :=
    quotient_integral_model hquotient
  obtain ⟨B, hBcube⟩ := dualA_is_cube hd hcop hcurve
  obtain ⟨a, b, hBcoord⟩ := n35O3_exists_coords B
  have hclass : dualA m n d =
      ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := by
    simpa [hBcoord] using hBcube
  have hm : m = n35NormForm a b :=
    m_eq_coord_norm_of_unit_cube (u := (1 : N35O3)) hcurve
      (by simp only [map_one, one_mul])
      (by simpa only [one_mul] using hclass)
  let C : ℤ := d * (24 * m + 12 * d ^ 2)
  let R : ℤ := a ^ 3 + b ^ 3 - 3 * a * b ^ 2
  let I : ℤ := 3 * a ^ 2 * b - 3 * a * b ^ 2
  have hcoords :
      ((n - C : ℤ) : N35O3) + ((-2 * C : ℤ) : N35O3) * n35Omega =
        (R : N35O3) + (I : N35O3) * n35Omega := by
    calc
      ((n - C : ℤ) : N35O3) +
          ((-2 * C : ℤ) : N35O3) * n35Omega =
          dualA m n d := by
        unfold dualA n35SqrtNegThree C
        push_cast
        ring
      _ = ((a : N35O3) + (b : N35O3) * n35Omega) ^ 3 := hclass
      _ = (R : N35O3) + (I : N35O3) * n35Omega := by
        rw [n35_coord_cube]
  have hreal : n - C = R := (n35_coords_injective hcoords).1
  have himag : -2 * C = I := (n35_coords_injective hcoords).2
  have hrealQ : ((n - C : ℤ) : ℚ) = (R : ℚ) := by
    exact_mod_cast hreal
  have himagQ : ((-2 * C : ℤ) : ℚ) = (I : ℚ) := by
    exact_mod_cast himag
  let u : ℚ := (2 * a - b : ℤ) / (2 * d : ℤ)
  let v : ℚ := (b : ℚ) / (2 * d : ℤ)
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hd)
  have hsuv : s = u ^ 2 + 3 * v ^ 2 := by
    rw [hs, hm]
    unfold u v n35NormForm
    push_cast
    field_simp [hdQ]
    ring
  have htuv : t = u ^ 3 - 9 * u * v ^ 2 := by
    rw [ht]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, R] at hrealQ
    dsimp [C, I] at himagQ
    push_cast at hrealQ himagQ
    linear_combination 8 * hrealQ - 4 * himagQ
  have himaguv :
      -(24 * s + 12) = 3 * u ^ 2 * v - 3 * v ^ 3 := by
    rw [hs]
    unfold u v
    push_cast
    field_simp [hdQ]
    dsimp [C, I] at himagQ
    push_cast at himagQ
    linear_combination 4 * himagQ
  have hrel :
      u ^ 2 * v + 8 * u ^ 2 - v ^ 3 + 24 * v ^ 2 + 4 = 0 := by
    rw [hsuv] at himaguv
    linear_combination (-1 / 3 : ℚ) * himaguv
  have hv8 : v + 8 ≠ 0 := by
    intro hv
    have hv' : v = -8 := by
      linarith
    rw [hv'] at hrel
    norm_num at hrel
    nlinarith
  let x : ℚ := -228 / (v + 8)
  let y : ℚ := u * x / 3
  have hx0 : x ≠ 0 := by
    unfold x
    exact div_ne_zero (by norm_num) hv8
  refine ⟨x, y, hx0, ?_, ?_, ?_⟩
  · exact inverse_good_identity hv8 hrel
  · exact inverse_x_identity hv8 hsuv hrel
  · exact inverse_y_identity hv8 htuv hrel

/-- The forward degree-three isogeny is surjective on rational points of
the small quotient. -/
theorem threeIsogenyPoint_surjective (Q : QuotientPoint) :
    ∃ P : GoodPoint, threeIsogenyPoint P = Q := by
  cases Q with
  | zero => exact ⟨0, threeIsogenyPoint_zero⟩
  | some s t h =>
      have hquotient : OnQuotient s t :=
        (quotientCurve_equation_iff s t).mp h.1
      obtain ⟨x, y, hx, hgood, hX, hY⟩ :=
        quotient_affine_has_threeIsogeny_preimage hquotient
      have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
        WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          ((goodCurve_equation_iff x y).mpr hgood)
      refine ⟨WeierstrassCurve.Affine.Point.some x y hns, ?_⟩
      rw [threeIsogenyPoint_some_of_x_ne_zero hns hx]
      change WeierstrassCurve.Affine.Point.some
          (threeIsogenyX x) (threeIsogenyY x y) _ =
        WeierstrassCurve.Affine.Point.some s t h
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩

end

end MazurProof.XDelta19GoodDualDescent
