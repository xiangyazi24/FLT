import FLT.Assumptions.MazurProof.RealTopologyS3
import FLT.Assumptions.MazurProof.RealTorsionBound

/-!
# No full 3-torsion: the elementary quartic obstruction

This file records the elementary real calculation behind the obstruction to
full rational 3-torsion.  The point/group-law bridge is not reproved here; the
core theorem below says that the third-division quartic cannot split as four
real roots at which the short cubic is positive on an elliptic short model.
-/

open Polynomial

namespace MazurProof

open RealTopology

/-- The third-division quartic for `y^2 = x^3 + A*x^2 + B*x`. -/
def shortPsi3 (A B x : ℝ) : ℝ :=
  3 * x ^ 4 + 4 * A * x ^ 3 + 6 * B * x ^ 2 - B ^ 2

/-- Formal second derivative of `shortCubic A B`. -/
def shortCubicSecondDeriv (A x : ℝ) : ℝ :=
  6 * x + 2 * A

/-- Polynomial form of `shortPsi3`, used for Vieta coefficient extraction. -/
noncomputable def shortPsi3Poly (A B : ℝ) : ℝ[X] :=
  monomial 4 3 + monomial 3 (4 * A) + monomial 2 (6 * B) - monomial 0 (B ^ 2)

private theorem esymm_four_one (r1 r2 r3 r4 : ℝ) :
    (r1 ::ₘ r2 ::ₘ r3 ::ₘ {r4} : Multiset ℝ).esymm 1 =
      r1 + r2 + r3 + r4 := by
  simp [Multiset.esymm, Multiset.powersetCard_one]
  ring_nf

private theorem esymm_four_same_two (c : ℝ) :
    (c ::ₘ c ::ₘ c ::ₘ {c} : Multiset ℝ).esymm 2 = 6 * c ^ 2 := by
  simp [Multiset.esymm, Multiset.powersetCard_one]
  ring_nf

private theorem esymm_four_same_four (c : ℝ) :
    (c ::ₘ c ::ₘ c ::ₘ {c} : Multiset ℝ).esymm 4 = c ^ 4 := by
  simp [Multiset.esymm, Multiset.powersetCard_one]
  ring_nf

@[simp] theorem shortPsi3Poly_eval (A B x : ℝ) :
    (shortPsi3Poly A B).eval x = shortPsi3 A B x := by
  simp [shortPsi3Poly, shortPsi3]

private theorem coeff_const_square_ne_zero (B : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((C B : ℝ[X]) ^ 2).coeff n = 0 := by
  rw [show (C B : ℝ[X]) ^ 2 = C (B ^ 2) by
    exact (map_pow (Polynomial.C : ℝ →+* ℝ[X]) B 2).symm]
  exact Polynomial.coeff_C_of_ne_zero (a := B ^ 2) (n := n) hn

private theorem coeff_const_square_zero (B : ℝ) :
    ((C B : ℝ[X]) ^ 2).coeff 0 = B ^ 2 := by
  rw [show (C B : ℝ[X]) ^ 2 = C (B ^ 2) by
    exact (map_pow (Polynomial.C : ℝ →+* ℝ[X]) B 2).symm]
  exact Polynomial.coeff_C_zero (a := B ^ 2)

/-- The requested ring identity for the third-division quartic. -/
theorem shortPsi3_identity (A B x : ℝ) :
    shortPsi3 A B x =
      2 * shortCubic A B x * shortCubicSecondDeriv A x -
        (shortCubicDeriv A B x) ^ 2 := by
  simp [shortPsi3, shortCubic, shortCubicDeriv, shortCubicSecondDeriv]
  ring

/-- A positive short-cubic value at a root of `ψ₃` lies to the right of `-A/3`. -/
theorem shortPsi3_root_ge_neg_third
    {A B x : ℝ} (hroot : shortPsi3 A B x = 0)
    (hgpos : 0 < shortCubic A B x) :
    -A / 3 ≤ x := by
  have hzero :
      2 * shortCubic A B x * shortCubicSecondDeriv A x -
        (shortCubicDeriv A B x) ^ 2 = 0 := by
    rw [← shortPsi3_identity, hroot]
  have hsq :
      (shortCubicDeriv A B x) ^ 2 =
        2 * shortCubic A B x * shortCubicSecondDeriv A x := by
    linarith
  have hprod_nonneg :
      0 ≤ 2 * shortCubic A B x * shortCubicSecondDeriv A x := by
    rw [← hsq]
    exact sq_nonneg _
  have hsecond_nonneg : 0 ≤ shortCubicSecondDeriv A x := by
    nlinarith
  simp [shortCubicSecondDeriv] at hsecond_nonneg
  nlinarith

private theorem shortPsi3_root_of_factorization_left
    {A B r1 r2 r3 r4 : ℝ}
    (hfac : shortPsi3Poly A B =
      C 3 * (({r1, r2, r3, r4} : Multiset ℝ).map (fun r => X - C r)).prod) :
    shortPsi3 A B r1 = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval r1) hfac
  simpa using h

private theorem shortPsi3_vieta_sum
    {A B r1 r2 r3 r4 : ℝ}
    (hfac : shortPsi3Poly A B =
      C 3 * (({r1, r2, r3, r4} : Multiset ℝ).map (fun r => X - C r)).prod) :
    r1 + r2 + r3 + r4 = -4 * A / 3 := by
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 3) hfac
  rw [coeff_C_mul, Multiset.prod_X_sub_C_coeff] at hcoeff
  · norm_num at hcoeff
    rw [esymm_four_one] at hcoeff
    simp [shortPsi3Poly, Polynomial.coeff_monomial] at hcoeff
    rw [coeff_const_square_ne_zero B (by norm_num : (3 : ℕ) ≠ 0)] at hcoeff
    ring_nf at hcoeff ⊢
    nlinarith
  · norm_num

private theorem shortPsi3_vieta_B
    {A B r1 r2 r3 r4 : ℝ}
    (h1 : r1 = -A / 3) (h2 : r2 = -A / 3)
    (h3 : r3 = -A / 3) (h4 : r4 = -A / 3)
    (hfac : shortPsi3Poly A B =
      C 3 * (({r1, r2, r3, r4} : Multiset ℝ).map (fun r => X - C r)).prod) :
    B = A ^ 2 / 3 := by
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 2) hfac
  rw [h1, h2, h3, h4] at hcoeff
  rw [coeff_C_mul, Multiset.prod_X_sub_C_coeff] at hcoeff
  · norm_num at hcoeff
    rw [esymm_four_same_two] at hcoeff
    simp [shortPsi3Poly, Polynomial.coeff_monomial] at hcoeff
    rw [coeff_const_square_ne_zero B (by norm_num : (2 : ℕ) ≠ 0)] at hcoeff
    ring_nf at hcoeff ⊢
    nlinarith
  · norm_num

private theorem shortPsi3_vieta_const
    {A B r1 r2 r3 r4 : ℝ}
    (h1 : r1 = -A / 3) (h2 : r2 = -A / 3)
    (h3 : r3 = -A / 3) (h4 : r4 = -A / 3)
    (hfac : shortPsi3Poly A B =
      C 3 * (({r1, r2, r3, r4} : Multiset ℝ).map (fun r => X - C r)).prod) :
    A ^ 4 / 27 = -B ^ 2 := by
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) hfac
  rw [h1, h2, h3, h4] at hcoeff
  rw [coeff_C_mul, Multiset.prod_X_sub_C_coeff] at hcoeff
  · norm_num at hcoeff
    rw [esymm_four_same_four] at hcoeff
    simp [shortPsi3Poly, Polynomial.coeff_monomial] at hcoeff
    rw [coeff_const_square_zero B] at hcoeff
    ring_nf at hcoeff ⊢
    nlinarith
  · norm_num

private theorem shortW_discriminant_noFull3 (A B : ℝ) :
    (shortW A B).Δ = 16 * B ^ 2 * (A ^ 2 - 4 * B) := by
  simp [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/--
The elementary real obstruction: an elliptic short model cannot have `ψ₃`
factor as four real roots all lying on the positive part of the real cubic.
-/
theorem shortPsi3_no_four_pos_roots_of_factorization
    (A B : ℝ) [(shortW A B).IsElliptic]
    {r1 r2 r3 r4 : ℝ}
    (hfac : shortPsi3Poly A B =
      C 3 * (({r1, r2, r3, r4} : Multiset ℝ).map (fun r => X - C r)).prod)
    (hpos1 : 0 < shortCubic A B r1)
    (hpos2 : 0 < shortCubic A B r2)
    (hpos3 : 0 < shortCubic A B r3)
    (hpos4 : 0 < shortCubic A B r4) :
    False := by
  have hroot1 := shortPsi3_root_of_factorization_left (A := A) (B := B)
    (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) hfac
  have hroot2 := shortPsi3_root_of_factorization_left (A := A) (B := B)
    (r1 := r2) (r2 := r1) (r3 := r3) (r4 := r4) (by
      simpa [Multiset.map_cons, mul_comm, mul_left_comm, mul_assoc] using hfac)
  have hroot3 := shortPsi3_root_of_factorization_left (A := A) (B := B)
    (r1 := r3) (r2 := r1) (r3 := r2) (r4 := r4) (by
      simpa [Multiset.map_cons, mul_comm, mul_left_comm, mul_assoc] using hfac)
  have hroot4 := shortPsi3_root_of_factorization_left (A := A) (B := B)
    (r1 := r4) (r2 := r1) (r3 := r2) (r4 := r3) (by
      simpa [Multiset.map_cons, mul_comm, mul_left_comm, mul_assoc] using hfac)
  have hge1 := shortPsi3_root_ge_neg_third hroot1 hpos1
  have hge2 := shortPsi3_root_ge_neg_third hroot2 hpos2
  have hge3 := shortPsi3_root_ge_neg_third hroot3 hpos3
  have hge4 := shortPsi3_root_ge_neg_third hroot4 hpos4
  have hsum := shortPsi3_vieta_sum (A := A) (B := B)
    (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) hfac
  have hr1 : r1 = -A / 3 := by nlinarith
  have hr2 : r2 = -A / 3 := by nlinarith
  have hr3 : r3 = -A / 3 := by nlinarith
  have hr4 : r4 = -A / 3 := by nlinarith
  have hB := shortPsi3_vieta_B hr1 hr2 hr3 hr4 hfac
  have hconst := shortPsi3_vieta_const hr1 hr2 hr3 hr4 hfac
  have hA : A = 0 := by
    have hconst' : A ^ 4 / 27 = -(A ^ 2 / 3) ^ 2 := by
      simpa [hB] using hconst
    have hA4 : A ^ 4 = 0 := by
      nlinarith
    have hA2sq : (A ^ 2) ^ 2 = 0 := by
      rw [← hA4]
      ring
    exact sq_eq_zero_iff.mp (sq_eq_zero_iff.mp hA2sq)
  have hB0 : B = 0 := by
    rw [hA] at hB
    norm_num at hB
    exact hB
  have hDelta_zero : (shortW A B).Δ = 0 := by
    rw [shortW_discriminant_noFull3, hA, hB0]
    norm_num
  exact WeierstrassCurve.IsElliptic.isUnit.ne_zero hDelta_zero

/-- The rational full-3-torsion case follows from the existing real torsion bound. -/
theorem no_full_3_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasFullRationalTorsion E 3 := by
  intro hfull
  have hle := fullRationalTorsion_order_le_two_route4B E (m := 3) (by norm_num) hfull
  norm_num at hle

end MazurProof
