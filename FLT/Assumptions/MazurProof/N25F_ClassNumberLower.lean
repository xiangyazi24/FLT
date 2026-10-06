import FLT.Assumptions.MazurProof.N25F_CertificateDivisors
import FLT.Assumptions.MazurProof.N25F_ClassNumberUpper

/-!
# The class number of the N25 curve is `71`

Let `α` be the degree-zero class of `Z - YZ`, the difference of two rational
points at infinity.

* `71 α = 0`: the divisor `71·Z - 71·YZ` is the divisor of the explicit
  function `z s⁻¹⁷ x⁻¹⁴ (x + y)²⁵` (`div_certificateUnit`).
* `α ≠ 0`: if `Z - YZ = div f`, then `f ∈ L(YZ)`, and by gonality `f` is
  constant, so `Z = YZ`, which is false.

Since `71` is prime, `α` has order `71` in `Pic⁰`, so `71` divides the class
number; combined with the upper bound `#Pic⁰ ≤ 71`
(`card_picDegreeZero_le_seventy_one`), the class number is exactly `71`.  No
Riemann–Roch input is used.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ClassNumberLower
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_FullPicardDegree
open N25F_RiemannRochSpace N25F_Gonality N25F_ClassNumberUpper
open N25F_OrderCalculus N25F_RationalPointOrders N25F_CertificateDivisors
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

theorem lof_nonneg (cX cYZ cZ cR cP : ℤ) (hX : 0 ≤ cX) (hYZ : 0 ≤ cYZ) (hZ : 0 ≤ cZ)
    (hR : 0 ≤ cR) (hP : 0 ≤ cP) (A : fullClosedPointGrading25Two.Atom) :
    0 ≤ lof cX cYZ cZ cR cP A := by
  classical
  simp only [lof, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- The class of `Z - YZ` in the full divisor-class group. -/
def alpha : fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two :=
  fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two (lof 0 (-1) 1 0 0)

theorem alpha_degree :
    fullClosedPointGrading25Two.classDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker alpha = 0 := by
  rw [alpha, fullClosedPointGrading25Two.classDegree_classOf, lof_degree]
  norm_num

/-- `71 α = 0`, by the explicit certificate. -/
theorem seventyOne_smul_alpha : (71 : ℕ) • alpha = 0 := by
  rw [alpha, ← map_nsmul]
  refine (QuotientAddGroup.eq_zero_iff ((71 : ℕ) • lof 0 (-1) 1 0 0)).mpr ?_
  have h : (71 : ℕ) • lof 0 (-1) 1 0 0 = lof 0 (-71) 71 0 0 := by
    rw [← natCast_zsmul, lof_zsmul]
    norm_num
  rw [h, ← div_certificateUnit]
  exact ⟨_, rfl⟩

/-- `α ≠ 0`, by gonality. -/
theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := (QuotientAddGroup.eq_zero_iff (lof 0 (-1) 1 0 0)).mp h
  set f : K := ((Additive.toMul g : Kˣ) : K) with hf
  have hf0 : f ≠ 0 := Units.ne_zero _
  have hgf : Additive.ofMul (Units.mk0 f hf0) = g := by
    apply Additive.toMul.injective
    ext
    rfl
  have hmem : f ∈ fullRiemannRochSpace25Two (lof 0 1 0 0 0) := by
    refine Or.inr ⟨hf0, fun A => ?_⟩
    rw [hgf, hg]
    have : lof 0 1 0 0 0 A + lof 0 (-1) 1 0 0 A = lof 0 0 1 0 0 A := by
      rw [← Finsupp.add_apply, lof_add]
      norm_num
    rw [this]
    exact lof_nonneg _ _ _ _ _ le_rfl le_rfl zero_le_one le_rfl le_rfl A
  rcases mem_fullRiemannRochSpace25Two_of_degree_le_two (lof 0 1 0 0 0)
      (lof_nonneg _ _ _ _ _ le_rfl zero_le_one le_rfl le_rfl le_rfl)
      (by rw [lof_degree]; norm_num) f hmem with h0 | h1
  · exact hf0 h0
  · have hg0 : g = 0 := by
      rw [← hgf]
      apply Additive.toMul.injective
      ext
      exact h1
    have := congrArg (fun D => D atomZ) hg
    simp only [hg0, map_zero, Finsupp.coe_zero, Pi.zero_apply, lof_apply_Z] at this
    exact absurd this (by norm_num)

/-- The degree-zero classes form the kernel of the class degree. -/
abbrev picZeroSubgroup :
    AddSubgroup (fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two) :=
  (fullClosedPointGrading25Two.classDegree fullProjectivePrincipalSubgroup25Two
    fullProjectivePrincipalSubgroup25Two_le_degree_ker).ker

/-- **The class number is `71`.** -/
theorem card_picDegreeZero_eq_seventy_one : Fintype.card (Pic25 0) = 71 := by
  haveI : Fact (Nat.Prime 71) := ⟨by norm_num⟩
  have hequiv : Pic25 0 ≃ picZeroSubgroup :=
    Equiv.subtypeEquivRight fun c => by simp [picZeroSubgroup, AddMonoidHom.mem_ker]
  have ha : alpha ∈ picZeroSubgroup := alpha_degree
  have horder : addOrderOf (⟨alpha, ha⟩ : picZeroSubgroup) = 71 := by
    apply addOrderOf_eq_prime
    · exact Subtype.ext seventyOne_smul_alpha
    · intro h
      exact alpha_ne_zero (congrArg Subtype.val h)
  have hdvd := addOrderOf_dvd_natCard (⟨alpha, ha⟩ : picZeroSubgroup)
  rw [horder, ← Nat.card_congr hequiv, Nat.card_eq_fintype_card] at hdvd
  have hle := card_picDegreeZero_le_seventy_one
  have hpos : 0 < Fintype.card (Pic25 0) := Fintype.card_pos_iff.mpr ⟨⟨alpha, alpha_degree⟩⟩
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

end MazurProof.N25F_ClassNumberLower
