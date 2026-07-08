import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN12Defs
import FLT.Assumptions.MazurProof.RationalPointsN12

/-!
# Kubert bridge: Z/2Z × Z/12Z torsion → point on w² = u³ - u² - 4u + 4

Reduces `Z2xZ12_gives_non_degenerate_N12_point` to a single
Kubert moduli input, with all polynomial identities proved by `ring`.

## The cyclic-12 Kubert family

For parameter `t ∈ ℚ`, define:
* `A₁₂(t) = 6t⁸ + 48t⁶ + 12t⁴ - 2`
* `B₁₂(t) = (t²-1)⁶(1+3t²)²`
* `E₁₂(t) : y² = x³ + A₁₂(t)x² + B₁₂(t)x`

## Key identity (PROVED by ring)

`A₁₂(t)² - 4B₁₂(t) = 256t⁶(t²+1)³(3t²-1)`

If this is a square `s²`, then removing the square factor `(16t²(t²+1))²`
gives `q² = (t²+1)(3t²-1)`, and setting `u = 3t²+1`, `w = 3tq` yields
`w² = u³ - u² - 4u + 4`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

def A12 (t : ℚ) : ℚ :=
  6 * t ^ 8 + 48 * t ^ 6 + 12 * t ^ 4 - 2

def B12 (t : ℚ) : ℚ := (t ^ 2 - 1) ^ 6 * (1 + 3 * t ^ 2) ^ 2

def Delta12 (t : ℚ) : ℚ :=
  256 * (t ^ 2 - 1) ^ 12 * (1 + 3 * t ^ 2) ^ 4 * t ^ 6 *
    (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1)

/-! ## Polynomial identities — all proved by ring/norm_num -/

theorem quad_disc_identity_12 (t : ℚ) :
    A12 t ^ 2 - 4 * B12 t = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) := by
  unfold A12 B12; ring

theorem delta12_zero_at_neg1 : Delta12 (-1) = 0 := by norm_num [Delta12]
theorem delta12_zero_at_0 : Delta12 0 = 0 := by norm_num [Delta12]
theorem delta12_zero_at_1 : Delta12 1 = 0 := by norm_num [Delta12]

/-! ## Square condition → obstruction curve point -/

theorem cover_square_of_square_12 {t s : ℚ} (ht : t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ q : ℚ, q ^ 2 = (t ^ 2 + 1) * (3 * t ^ 2 - 1) := by
  refine ⟨s / (16 * t ^ 3 * (t ^ 2 + 1)), ?_⟩
  have hdenom : (16 : ℚ) * t ^ 3 * (t ^ 2 + 1) ≠ 0 := by positivity
  have hdisc := quad_disc_identity_12 t
  have hs2 : s ^ 2 = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) :=
    hs.trans hdisc
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hdenom)]
  calc
    s ^ 2 = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) := hs2
    _ = ((t ^ 2 + 1) * (3 * t ^ 2 - 1)) *
        (16 * t ^ 3 * (t ^ 2 + 1)) ^ 2 := by ring

theorem obstruction_point_of_square_12 {t s : ℚ} (ht : t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ w : ℚ, w ^ 2 = (3 * t ^ 2 + 1) ^ 3 - (3 * t ^ 2 + 1) ^ 2
                      - 4 * (3 * t ^ 2 + 1) + 4 := by
  refine ⟨3 * s / (16 * t ^ 2 * (t ^ 2 + 1)), ?_⟩
  have hdenom : (16 : ℚ) * t ^ 2 * (t ^ 2 + 1) ≠ 0 := by positivity
  have hdisc := quad_disc_identity_12 t
  have hs2 : s ^ 2 = 256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1) :=
    hs.trans hdisc
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hdenom)]
  calc (3 * s) ^ 2
      = 9 * s ^ 2 := by ring
    _ = 9 * (256 * t ^ 6 * (t ^ 2 + 1) ^ 3 * (3 * t ^ 2 - 1)) := by rw [hs2]
    _ = ((3 * t ^ 2 + 1) ^ 3 - (3 * t ^ 2 + 1) ^ 2 - 4 * (3 * t ^ 2 + 1) + 4) *
        (16 * t ^ 2 * (t ^ 2 + 1)) ^ 2 := by ring

theorem non_degenerate_of_square_12 {t s : ℚ}
    (hΔ : Delta12 t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u := by
  have ht : t ≠ 0 := by
    intro h; exact hΔ (by rw [h]; exact delta12_zero_at_0)
  obtain ⟨w, hw⟩ := obstruction_point_of_square_12 ht hs
  refine ⟨3 * t ^ 2 + 1, w, by unfold E_N12_AffineEquation; linarith, ?_⟩
  intro hdeg
  unfold E_N12_DegenerateParameter at hdeg
  rcases hdeg with h | h | h | h | h
  · -- u = -2: 3t²+1 = -2 impossible since t² ≥ 0
    nlinarith [sq_nonneg t]
  · -- u = 0: 3t²+1 = 0 impossible since t² ≥ 0
    nlinarith [sq_nonneg t]
  · -- u = 1: 3t²+1 = 1 ⇒ t = 0, contradicting Delta12 t ≠ 0
    have h1 : t ^ 2 = 0 := by linarith
    exact ht ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1)
  · -- u = 2: 3t²+1 = 2 ⇒ 3t²-1 = 0 ⇒ Delta12 t = 0
    exact hΔ (by
      have h3t : 3 * t ^ 2 - 1 = 0 := by linarith
      unfold Delta12; rw [h3t, mul_zero])
  · -- u = 4: 3t²+1 = 4 ⇒ t²-1 = 0 ⇒ Delta12 t = 0
    exact hΔ (by
      have ht1 : t ^ 2 - 1 = 0 := by linarith
      unfold Delta12; rw [ht1]; ring)

theorem signed_residual_of_square_12 {t s : ℚ}
    (hΔ : Delta12 t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    RationalPointsN12.RationalCoverSignedResidual t := by
  have ht : t ≠ 0 := by
    intro h; exact hΔ (by rw [h]; exact delta12_zero_at_0)
  obtain ⟨q, hq⟩ := cover_square_of_square_12 ht hs
  rcases RationalPointsN12.rational_kubert_cover_degenerate_or_signedResidual t q hq
      with hdeg | hres
  · rcases hdeg with ht1 | htneg1
    · exact False.elim (hΔ (by rw [ht1]; exact delta12_zero_at_1))
    · exact False.elim (hΔ (by rw [htneg1]; exact delta12_zero_at_neg1))
  · exact hres

theorem factorIdentityResidual_of_square_12 {t s : ℚ}
    (hΔ : Delta12 t ≠ 0)
    (hs : s ^ 2 = A12 t ^ 2 - 4 * B12 t) :
    ∃ T D Y m n b r s₀ a c : ℤ,
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
      RationalPointsN12.NonAxisSignedResidual m n b r s₀ ∧
      RationalPointsN12.NonAxisFactorIdentityResidual m n a c := by
  exact RationalPointsN12.rationalCoverSignedResidual_factorIdentityResidual
    (signed_residual_of_square_12 hΔ hs)

/-! ## Checked group-theoretic extraction from `ZMod 2 × ZMod 12` -/

private def zmod12ToZmod2xZmod12 : ZMod 12 →+ (ZMod 2 × ZMod 12) where
  toFun x := (0, x)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp

private theorem zmod12ToZmod2xZmod12_injective :
    Function.Injective zmod12ToZmod2xZmod12 := by
  intro x y h
  exact congrArg Prod.snd h

private theorem addOrderOf_zmod2x12_zero_one :
    addOrderOf ((0, 1) : ZMod 2 × ZMod 12) = 12 := by
  have h := addOrderOf_injective
    zmod12ToZmod2xZmod12 zmod12ToZmod2xZmod12_injective (1 : ZMod 12)
  simpa [zmod12ToZmod2xZmod12, ZMod.addOrderOf_one] using h

/-- The injection supplies a rational point of additive order `12`. -/
theorem point_addOrder12_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, addOrderOf P = 12 := by
  refine ⟨f ((0, 1) : ZMod 2 × ZMod 12), ?_⟩
  have h := addOrderOf_injective f hf ((0, 1) : ZMod 2 × ZMod 12)
  simpa [addOrderOf_zmod2x12_zero_one] using h

/-- Multiplicative-order wrapper for APIs stated through `Multiplicative.ofAdd`. -/
theorem point_order12_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, orderOf (Multiplicative.ofAdd P) = 12 := by
  rcases point_addOrder12_of_zmod2_zmod12_injection E f hf with ⟨P, hP⟩
  exact ⟨P, by simpa using hP⟩

private def zmod2ToZmod12_six : ZMod 2 →+ ZMod 12 where
  toFun x := if x = 0 then 0 else 6
  map_zero' := by
    simp
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

private theorem zmod2ToZmod12_six_injective :
    Function.Injective zmod2ToZmod12_six := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · exfalso
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change
      (if (0 : ZMod 2) = 0 then (0 : ZMod 12) else 6) =
        (if (1 : ZMod 2) = 0 then (0 : ZMod 12) else 6) at h
    simp only [if_true, if_false, h10] at h
    exact (by decide : ¬ ((0 : ZMod 12) = 6)) h
  · exfalso
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change
      (if (1 : ZMod 2) = 0 then (0 : ZMod 12) else 6) =
        (if (0 : ZMod 2) = 0 then (0 : ZMod 12) else 6) at h
    simp only [if_true, if_false, h10] at h
    exact (by decide : ¬ ((6 : ZMod 12) = 0)) h
  · rfl

private def zmod2x2ToZmod2x12 :
    (ZMod 2 × ZMod 2) →+ (ZMod 2 × ZMod 12) where
  toFun x := (x.1, zmod2ToZmod12_six x.2)
  map_zero' := by
    ext <;> simp [zmod2ToZmod12_six]
  map_add' := by
    intro x y
    ext
    · simp
    · exact map_add zmod2ToZmod12_six x.2 y.2

private theorem zmod2x2ToZmod2x12_injective :
    Function.Injective zmod2x2ToZmod2x12 := by
  intro x y h
  apply Prod.ext
  · have hfst :
        (zmod2x2ToZmod2x12 x).1 = (zmod2x2ToZmod2x12 y).1 :=
      congrArg Prod.fst h
    simpa [zmod2x2ToZmod2x12] using hfst
  · have hsnd :
        (zmod2x2ToZmod2x12 x).2 = (zmod2x2ToZmod2x12 y).2 :=
      congrArg Prod.snd h
    exact zmod2ToZmod12_six_injective (by
      simpa [zmod2x2ToZmod2x12] using hsnd)

/-- The injection contains a checked copy of full rational `2`-torsion. -/
theorem full_two_torsion_of_zmod2_zmod12_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g := by
  refine ⟨f.comp zmod2x2ToZmod2x12, ?_⟩
  intro x y hxy
  apply zmod2x2ToZmod2x12_injective
  apply hf
  exact hxy

/-! ## The Tate/Kubert bridge seam -/

theorem square_discriminant_of_quadratic_root_12 {t x : ℚ}
    (hx : x ^ 2 + A12 t * x + B12 t = 0) :
    (2 * x + A12 t) ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  calc
    (2 * x + A12 t) ^ 2 =
        4 * (x ^ 2 + A12 t * x + B12 t) + (A12 t ^ 2 - 4 * B12 t) := by
      ring
    _ = A12 t ^ 2 - 4 * B12 t := by rw [hx]; ring

/-- If `E/ℚ` has a subgroup isomorphic to `ℤ/2ℤ × ℤ/12ℤ`, then `E` arises
from the cyclic-12 Kubert family with non-degenerate parameter, and the
remaining quadratic factor of the 2-torsion polynomial has a rational root. -/
theorem kubert_C12_tate_quadratic_root_of_order12_and_full_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h12 : ∃ P : (E⁄ℚ).Point, orderOf (Multiplicative.ofAdd P) = 12)
    (h2 : ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g) :
    ∃ t x : ℚ, Delta12 t ≠ 0 ∧ x ^ 2 + A12 t * x + B12 t = 0 := by
  sorry

/-- Checked reduction from a `ZMod 2 × ZMod 12` injection to the Tate/Kubert
normal-form root seam. -/
theorem kubert_C12_tate_quadratic_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t x : ℚ, Delta12 t ≠ 0 ∧ x ^ 2 + A12 t * x + B12 t = 0 := by
  obtain ⟨f, hf⟩ := hE
  exact kubert_C12_tate_quadratic_root_of_order12_and_full_two E
    (point_order12_of_zmod2_zmod12_injection E f hf)
    (full_two_torsion_of_zmod2_zmod12_injection E f hf)

/-- If `E/ℚ` has a subgroup isomorphic to `ℤ/2ℤ × ℤ/12ℤ`, then `E` arises
from the cyclic-12 Kubert family with non-degenerate parameter, making the
quadratic factor of the 2-torsion polynomial have square discriminant. -/
theorem kubert_C12_square
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t s : ℚ, Delta12 t ≠ 0 ∧ s ^ 2 = A12 t ^ 2 - 4 * B12 t := by
  obtain ⟨t, x, hΔ, hx⟩ := kubert_C12_tate_quadratic_root E hE
  exact ⟨t, 2 * x + A12 t, hΔ, square_discriminant_of_quadratic_root_12 hx⟩

/-- Discharge `Z2xZ12_gives_non_degenerate_N12_point` from the Kubert square bridge. -/
theorem bridge_N12 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N12_AffineEquation u w ∧ ¬ E_N12_DegenerateParameter u := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C12_square E hE
  exact non_degenerate_of_square_12 hΔ hs

theorem bridge_N12_signedResidual (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t : ℚ, Delta12 t ≠ 0 ∧ RationalPointsN12.RationalCoverSignedResidual t := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C12_square E hE
  exact ⟨t, hΔ, signed_residual_of_square_12 hΔ hs⟩

theorem bridge_N12_factorIdentityResidual (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ t : ℚ, ∃ T D Y m n b r s₀ a c : ℤ,
      Delta12 t ≠ 0 ∧
      0 < D ∧ Int.gcd T D = 1 ∧ t = (T : ℚ) / (D : ℚ) ∧
      Y ^ 2 = (T ^ 2 + D ^ 2) * (3 * T ^ 2 - D ^ 2) ∧
      RationalPointsN12.NonAxisSignedResidual m n b r s₀ ∧
      RationalPointsN12.NonAxisFactorIdentityResidual m n a c := by
  obtain ⟨t, s, hΔ, hs⟩ := kubert_C12_square E hE
  obtain ⟨T, D, Y, m, n, b, r, s₀, a, c, hDpos, hcop, ht, hcover,
    hsigned, hfactor⟩ := factorIdentityResidual_of_square_12 hΔ hs
  exact ⟨t, T, D, Y, m, n, b, r, s₀, a, c, hΔ, hDpos, hcop, ht, hcover,
    hsigned, hfactor⟩

theorem bridge_N12_constrainedFactorIdentityResidual
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ m n a c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
      RationalPointsN12.NonAxisFactorIdentityResidual m n a c := by
  obtain ⟨_, _, hres⟩ := bridge_N12_signedResidual E hE
  exact RationalPointsN12.rationalCoverSignedResidual_constrainedFactorIdentityResidual hres

theorem no_Z2xZ12_of_F_boundary
    (hFbd : ∀ {X Y : ℚ}, RationalPointsN12.F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f) :
    False := by
  obtain ⟨m, n, a, c, hmn0, _hcop, hpar, hres⟩ :=
    bridge_N12_constrainedFactorIdentityResidual E hE
  exact RationalPointsN12.no_nonAxisFactorIdentityResidual_of_F_boundary
    hFbd hmn0 hpar hres

theorem no_Z2xZ12_torsion_of_F_boundary
    (hFbd : ∀ {X Y : ℚ}, RationalPointsN12.F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point, Function.Injective f := by
  intro hE
  exact no_Z2xZ12_of_F_boundary hFbd E hE

end

end MazurProof.KubertBridgeN12
