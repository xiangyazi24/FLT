import FLT.Assumptions.MazurProof.N18MumfordIdeal
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# Explicit invertibility of N18 Mumford ideals

For a semi-Mumford pair `(u,v)`, squarefreeness of the fixed sextic gives
`(u,2v,(f-v²)/u)=1`.  Consequently

`(u,y-v) (u,y+v) = (u)`.

This packages `(u,y-v)` as a unit of the fractional-ideal monoid without a
Dedekind-domain instance for the affine coordinate ring.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem mumford_bezout (D : SemiMumford K) :
    ∃ w a b c : K[X],
      f K - D.v ^ 2 = D.u * w ∧
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  classical
  obtain ⟨w, hw⟩ := D.curve_dvd
  have hcop : IsCoprime D.u (EuclideanDomain.gcd (2 * D.v) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact D.u_monic.ne_zero hzero.1
    · intro z hz hzu hzg
      have hz2v : z ∣ 2 * D.v :=
        hzg.trans (EuclideanDomain.gcd_dvd_left (2 * D.v) w)
      have hzw : z ∣ w :=
        hzg.trans (EuclideanDomain.gcd_dvd_right (2 * D.v) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq : C (2 : K) = (2 : K[X]) := by
          exact map_natCast (C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr (by norm_num) : IsUnit (2 : K))
      have hzv : z ∣ D.v := by
        rcases hz.prime.dvd_mul.mp hz2v with hz2 | hzv
        · exact (hz.not_isUnit (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzv
      have hzzSub : z * z ∣ f K - D.v ^ 2 := by
        rw [hw]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ D.v ^ 2 := by
        simpa only [pow_two] using mul_dvd_mul hzv hzv
      have hzzF : z * z ∣ f K := by
        simpa only [sub_add_cancel] using dvd_add hzzSub hzzSq
      exact ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
        (f_monic K).ne_zero).mp (f_squarefree K) z hz) hzzF
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨w, a,
    b * EuclideanDomain.gcdA (2 * D.v) w,
    b * EuclideanDomain.gcdB (2 * D.v) w, hw, ?_⟩
  rw [← hab, EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass K v ∈ mumfordIdeal K u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_mul_conj_integral (D : SemiMumford K) :
    mumfordIdeal K D.u D.v * mumfordIdeal K D.u (-D.v) =
      Ideal.span ({xClass K D.u} : Set (CoordinateRing K)) := by
  let I := mumfordIdeal K D.u D.v
  let J := mumfordIdeal K D.u (-D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨p₀ * q₀ * xClass K D.u +
        p₀ * qY * ySubClass K (-D.v) +
        pY * q₀ * ySubClass K D.v +
        pY * qY * xClass K w, ?_⟩
    rw [← hpEq, ← hqEq]
    simp only [mumfordIdeal, ySubClass, xClass_neg, sub_neg_eq_add] at hpEq hqEq ⊢
    have hgraph :
        (yClass K - xClass K D.v) * (yClass K + xClass K D.v) =
          xClass K D.u * xClass K w := by
      calc
        (yClass K - xClass K D.v) * (yClass K + xClass K D.v) =
            yClass K ^ 2 - xClass K D.v ^ 2 := by ring
        _ = xClass K (f K) - xClass K (D.v ^ 2) := by
          rw [yClass_sq, xClass_pow]
        _ = xClass K (f K - D.v ^ 2) := by rw [xClass_sub]
        _ = xClass K (D.u * w) := by rw [hw]
        _ = xClass K D.u * xClass K w := by rw [xClass_mul]
    linear_combination pY * qY * hgraph
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨w, a, b, c, hw, hbez⟩ := mumford_bezout K D
    have huI : xClass K D.u ∈ I :=
      xClass_mem_mumfordIdeal K D.u D.v
    have huJ : xClass K D.u ∈ J :=
      xClass_mem_mumfordIdeal K D.u (-D.v)
    have hvI : ySubClass K D.v ∈ I :=
      ySubClass_mem_mumfordIdeal K D.u D.v
    have hvJ : ySubClass K (-D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal K D.u (-D.v)
    have hu2 : xClass K D.u * xClass K D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv : xClass K D.u * xClass K (2 * D.v) ∈ I * J := by
      have hp : xClass K D.u * ySubClass K (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm : ySubClass K D.v * xClass K D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add, xClass_mul]
      change xClass K D.u * (2 * xClass K D.v) =
        xClass K D.u * (yClass K + xClass K D.v) -
          (yClass K - xClass K D.v) * xClass K D.u
      ring
    have huw : xClass K D.u * xClass K w ∈ I * J := by
      have hg : ySubClass K D.v * ySubClass K (-D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      convert hg using 1
      simp only [ySubClass, xClass_neg, sub_neg_eq_add]
      calc
        xClass K D.u * xClass K w = xClass K (D.u * w) := by
          rw [xClass_mul]
        _ = xClass K (f K - D.v ^ 2) := by rw [hw]
        _ = xClass K (f K) - xClass K (D.v ^ 2) := by rw [xClass_sub]
        _ = yClass K ^ 2 - xClass K D.v ^ 2 := by
          rw [yClass_sq, xClass_pow]
        _ = (yClass K - xClass K D.v) *
            (yClass K + xClass K D.v) := by ring
    have ha : xClass K a * (xClass K D.u * xClass K D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass K a) hu2
    have hb : xClass K b *
        (xClass K D.u * xClass K (2 * D.v)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass K b) huv
    have hc : xClass K c * (xClass K D.u * xClass K w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass K c) huw
    have hsum := Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass K a * (xClass K D.u * xClass K D.u) +
            xClass K b * (xClass K D.u * xClass K (2 * D.v)) +
            xClass K c * (xClass K D.u * xClass K w) =
          xClass K D.u := by
      calc
        _ = xClass K D.u *
            xClass K (a * D.u + b * (2 * D.v) + c * w) := by
              simp only [xClass_add, xClass_mul]
              ring
        _ = xClass K D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass K D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford K) :
    (mumfordIdeal K D.u D.v :
        FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) *
      (mumfordIdeal K D.u (-D.v) :
        FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) =
      (Ideal.span ({xClass K D.u} : Set (CoordinateRing K)) :
        FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

def mumfordIdealUnit (D : SemiMumford K) : InvFrac K :=
  Units.mkOfMulEqOne
    (mumfordIdeal K D.u D.v :
      FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))
    ((mumfordIdeal K D.u (-D.v) :
        FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) *
      (Ideal.span ({xClass K D.u} : Set (CoordinateRing K)) :
        FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        (FunctionField K) (xClass_ne_zero K D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford K) :
    (mumfordIdealUnit K D :
      FractionalIdeal (CoordinateRing K)⁰ (FunctionField K)) =
      mumfordIdeal K D.u D.v := rfl

end

end MazurProof.N18Mumford
