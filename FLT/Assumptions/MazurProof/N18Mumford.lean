import FLT.Assumptions.MazurProof.N18RouteC_Split
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Balanced Mumford data and oriented ideal semantics for the N18 sextic

The executable representation is the balanced triple `(u,v,nInf)`.  Its
semantic target is an oriented fractional-ideal quotient: an invertible
fractional ideal of the two-infinity affine coordinate ring, together with an
integer recording the order at the chosen positive infinity.

This file deliberately separates the polynomial data from the noncomputable
semantic quotient.  Later sections install the Mumford ideal as an invertible
fractional ideal, prove the canonical normal-form theorem, and inherit all
group laws from the quotient.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-! ## The affine coordinate ring -/

def f : K[X] :=
  X ^ 6 + 4 * X ^ 5 + 10 * X ^ 4 + 10 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1

private def fQ : ℚ[X] :=
  X ^ 6 + 4 * X ^ 5 + 10 * X ^ 4 + 10 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1

theorem f_monic : (f K).Monic := by
  unfold f
  monicity!

theorem f_natDegree : (f K).natDegree = 6 := by
  unfold f
  compute_degree!

private def bezoutA : ℚ[X] :=
  60 * X ^ 4 + 80 * X ^ 3 + 150 * X ^ 2 - 120 * X + 178

private def bezoutB : ℚ[X] :=
  -10 * X ^ 5 - 20 * X ^ 4 - 45 * X ^ 3 + 20 * X ^ 2 - 33 * X - 17

private theorem C_nat (n : ℕ) : C (n : ℚ) = (n : ℚ[X]) := by
  exact map_natCast (C : ℚ →+* ℚ[X]) n

private theorem fQ_derivative : fQ.derivative =
    6 * X ^ 5 + 20 * X ^ 4 + 40 * X ^ 3 + 30 * X ^ 2 + 10 * X + 2 := by
  simp only [fQ, derivative_add, derivative_one, derivative_X, derivative_pow,
    derivative_ofNat, derivative_mul, zero_mul, zero_add, add_zero]
  rw [C_nat 2, C_nat 3, C_nat 4, C_nat 5, C_nat 6]
  ring

private theorem f_bezout_derivative :
    bezoutA * fQ + bezoutB * fQ.derivative = 144 := by
  rw [fQ_derivative]
  simp only [bezoutA, bezoutB, fQ]
  ring

private theorem fQ_separable : fQ.Separable := by
  rw [separable_def']
  refine ⟨C (1 / 144 : ℚ) * bezoutA, C (1 / 144 : ℚ) * bezoutB, ?_⟩
  calc
    (C (1 / 144 : ℚ) * bezoutA) * fQ +
        (C (1 / 144 : ℚ) * bezoutB) * fQ.derivative =
      C (1 / 144 : ℚ) * (bezoutA * fQ + bezoutB * fQ.derivative) := by ring
    _ = C (1 / 144 : ℚ) * 144 := by rw [f_bezout_derivative]
    _ = C (1 / 144 : ℚ) * C 144 := by rw [C_ofNat]
    _ = 1 := by rw [← C_mul]; norm_num

private theorem f_eq_map :
    f K = fQ.map (algebraMap ℚ K) := by
  simp [f, fQ]

theorem f_separable : (f K).Separable := by
  rw [f_eq_map]
  exact (separable_map (algebraMap ℚ K)).mpr fQ_separable

theorem f_squarefree : Squarefree (f K) :=
  (f_separable K).squarefree

/-- The outer variable is `Y`; coefficients are polynomials in `X`. -/
def curvePoly : K[X][X] := X ^ 2 - C (f K)

theorem curvePoly_monic : (curvePoly K).Monic := by
  unfold curvePoly
  monicity!

theorem curvePoly_natDegree : (curvePoly K).natDegree = 2 := by
  unfold curvePoly
  compute_degree!

private theorem curvePoly_not_isRoot (q : K[X]) : ¬ IsRoot (curvePoly K) q := by
  intro hq
  have hsq : q ^ 2 = f K := by
    simpa only [IsRoot.def, curvePoly, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hq
  have hqunit : IsUnit q := by
    apply f_squarefree K q
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit (f K) := by
    rw [← hsq]
    exact hqunit.pow 2
  exact Polynomial.not_isUnit_of_natDegree_pos (f K)
    (by rw [f_natDegree]; norm_num) hfunit

theorem curvePoly_irreducible : Irreducible (curvePoly K) := by
  rw [(curvePoly_monic K).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot K q
      ((mem_roots (curvePoly_monic K).ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible (curvePoly K)) :=
  ⟨curvePoly_irreducible K⟩

abbrev CoordinateRing : Type u := AdjoinRoot (curvePoly K)

abbrev FunctionField : Type u := FractionRing (CoordinateRing K)

instance : IsDomain (CoordinateRing K) :=
  AdjoinRoot.isDomain_of_prime (curvePoly_irreducible K).prime

noncomputable instance : Algebra K (CoordinateRing K) := inferInstance
noncomputable instance : Algebra K[X] (CoordinateRing K) := inferInstance

def mk : K[X][X] →+* CoordinateRing K := AdjoinRoot.mk (curvePoly K)

def xClass (p : K[X]) : CoordinateRing K := mk K (C p)

def yClass : CoordinateRing K := mk K X

@[simp] theorem yClass_sq : yClass K ^ 2 = xClass K (f K) := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [yClass, xClass, mk, curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) : xClass K p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (curvePoly_monic K)
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Balanced triples -/

structure Mumford where
  u : K[X]
  v : K[X]
  nInf : ℕ
  u_monic : u.Monic
  deg_u : u.natDegree ≤ 2
  v_reduced : v % u = v
  curve_dvd : u ∣ f K - v ^ 2
  infinity_bound : u.natDegree + nInf ≤ 2

structure SemiMumford where
  u : K[X]
  v : K[X]
  nInf : ℤ
  u_monic : u.Monic
  v_reduced : v % u = v
  curve_dvd : u ∣ f K - v ^ 2

def zero : Mumford K where
  u := 1
  v := 0
  nInf := 1
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

@[simp] theorem zero_u : (zero K).u = 1 := rfl
@[simp] theorem zero_v : (zero K).v = 0 := rfl
@[simp] theorem zero_nInf : (zero K).nInf = 1 := rfl

/-! ## Mumford ideals -/

def ySubClass (v : K[X]) : CoordinateRing K := yClass K - xClass K v

def mumfordIdeal (u v : K[X]) : Ideal (CoordinateRing K) :=
  Ideal.span {xClass K u, ySubClass K v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass K u ∈ mumfordIdeal K u v := by
  exact Ideal.subset_span (by simp)

theorem mumfordIdeal_ne_bot (D : Mumford K) :
    mumfordIdeal K D.u D.v ≠ ⊥ := by
  intro hbot
  have hx : xClass K D.u = 0 := by
    have hm := xClass_mem_mumfordIdeal K D.u D.v
    rw [hbot, Ideal.mem_bot] at hm
    exact hm
  exact xClass_ne_zero K D.u_monic.ne_zero hx

/-! ## The oriented fractional-ideal quotient -/

abbrev InvFrac : Type u :=
  (FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))ˣ

abbrev OrientedFrac : Type u := InvFrac K × Multiplicative ℤ

/-- The one local datum used by the oriented quotient.  A concrete instance
for the positive infinity is constructed below the normal-form layer; it is
kept as data here so the quotient API can be developed independently. -/
structure InfinityOrder where
  ordPlus : (FunctionField K)ˣ →* Multiplicative ℤ

def principalOriented (O : InfinityOrder K) :
    (FunctionField K)ˣ →* OrientedFrac K :=
  (toPrincipalIdeal (CoordinateRing K) (FunctionField K)).prod O.ordPlus

abbrev OrientedPic (O : InfinityOrder K) : Type u :=
  Additive (OrientedFrac K ⧸ (principalOriented K O).range)

instance (O : InfinityOrder K) : AddCommGroup (OrientedPic K O) := inferInstance

def orientedMk (O : InfinityOrder K) :
    Additive (OrientedFrac K) →+ OrientedPic K O :=
  MonoidHom.toAdditive (QuotientGroup.mk' (principalOriented K O).range)

end

end MazurProof.N18Mumford
