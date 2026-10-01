import Mathlib

/-!
# The explicit cubic splitting data for the order-18 route

This file contains only exact algebra.  We present the real cubic splitting
field using the Eisenstein uniformizer `pi`, satisfying

`pi ^ 3 + 3 * pi ^ 2 - 3 = 0`,

and put `a = pi + 1`.  Thus `a ^ 3 = 3 * a + 1`.  All certificates below
are polynomial identities in this one relation.
-/

open Polynomial

namespace MazurProof.N18RouteC

noncomputable section

/-! ## The cyclic cubic field -/

def cubicPolyInt : ℤ[X] := X ^ 3 + 3 * X ^ 2 - 3

def cubicPoly : ℚ[X] := cubicPolyInt.map (algebraMap ℤ ℚ)

private theorem cubicPolyInt_monic : cubicPolyInt.Monic := by
  unfold cubicPolyInt
  monicity!

private theorem cubicPolyInt_natDegree : cubicPolyInt.natDegree = 3 := by
  unfold cubicPolyInt
  compute_degree!

private theorem cubicPolyInt_eisenstein_three :
    cubicPolyInt.IsEisensteinAt (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hPne : P ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  refine cubicPolyInt_monic.isEisensteinAt_of_mem_of_notMem hPne ?_ ?_
  · intro n hn
    rw [cubicPolyInt_natDegree] at hn
    interval_cases n <;>
      norm_num [cubicPolyInt, coeff_X_pow, coeff_X, P, Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [cubicPolyInt]

private theorem cubicPolyInt_irreducible : Irreducible cubicPolyInt := by
  apply cubicPolyInt_eisenstein_three.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  · exact cubicPolyInt_monic.isPrimitive
  · rw [cubicPolyInt_natDegree]
    norm_num

theorem cubicPoly_irreducible : Irreducible cubicPoly := by
  exact
    (cubicPolyInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
      cubicPolyInt_irreducible

instance cubicPolyIrreducibleFact : Fact (Irreducible cubicPoly) :=
  ⟨cubicPoly_irreducible⟩

theorem cubicPoly_monic : cubicPoly.Monic := by
  rw [cubicPoly]
  exact cubicPolyInt_monic.map (algebraMap ℤ ℚ)

theorem cubicPoly_natDegree : cubicPoly.natDegree = 3 := by
  rw [cubicPoly, cubicPolyInt_monic.natDegree_map (algebraMap ℤ ℚ)]
  exact cubicPolyInt_natDegree

abbrev L : Type := AdjoinRoot cubicPoly

def pi : L := AdjoinRoot.root cubicPoly

def a : L := pi + 1

theorem cubicPoly_eq : cubicPoly = X ^ 3 + 3 * X ^ 2 - 3 := by
  ext n
  simp [cubicPoly, cubicPolyInt]

theorem pi_relation : pi ^ 3 + 3 * pi ^ 2 - 3 = 0 := by
  change AdjoinRoot.mk cubicPoly (X ^ 3 + 3 * X ^ 2 - 3) = 0
  rw [← cubicPoly_eq, AdjoinRoot.mk_self]

@[simp] theorem pi_cubed : pi ^ 3 = 3 - 3 * pi ^ 2 := by
  linear_combination pi_relation

@[simp] theorem a_cubic : a ^ 3 = 3 * a + 1 := by
  unfold a
  calc
    (pi + 1) ^ 3 = pi ^ 3 + 3 * pi ^ 2 + 3 * pi + 1 := by ring
    _ = 3 * (pi + 1) + 1 := by rw [pi_cubed]; ring

@[simp] theorem a_pow_four : a ^ 4 = 3 * a ^ 2 + a := by
  calc
    a ^ 4 = a * a ^ 3 := by ring
    _ = 3 * a ^ 2 + a := by rw [a_cubic]; ring

@[simp] theorem a_pow_five : a ^ 5 = a ^ 2 + 9 * a + 3 := by
  calc
    a ^ 5 = a * a ^ 4 := by ring
    _ = a ^ 2 + 9 * a + 3 := by
      rw [a_pow_four]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_six : a ^ 6 = 9 * a ^ 2 + 6 * a + 1 := by
  calc
    a ^ 6 = (a ^ 3) ^ 2 := by ring
    _ = 9 * a ^ 2 + 6 * a + 1 := by rw [a_cubic]; ring

@[simp] theorem a_pow_seven : a ^ 7 = 6 * a ^ 2 + 28 * a + 9 := by
  calc
    a ^ 7 = a * a ^ 6 := by ring
    _ = 6 * a ^ 2 + 28 * a + 9 := by
      rw [a_pow_six]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_eight : a ^ 8 = 28 * a ^ 2 + 27 * a + 6 := by
  calc
    a ^ 8 = a * a ^ 7 := by ring
    _ = 28 * a ^ 2 + 27 * a + 6 := by
      rw [a_pow_seven]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_nine : a ^ 9 = 27 * a ^ 2 + 90 * a + 28 := by
  calc
    a ^ 9 = a * a ^ 8 := by ring
    _ = 27 * a ^ 2 + 90 * a + 28 := by
      rw [a_pow_eight]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_ten : a ^ 10 = 90 * a ^ 2 + 109 * a + 27 := by
  calc
    a ^ 10 = a * a ^ 9 := by ring
    _ = 90 * a ^ 2 + 109 * a + 27 := by
      rw [a_pow_nine]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_eleven : a ^ 11 = 109 * a ^ 2 + 297 * a + 90 := by
  calc
    a ^ 11 = a * a ^ 10 := by ring
    _ = 109 * a ^ 2 + 297 * a + 90 := by
      rw [a_pow_ten]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_twelve : a ^ 12 = 297 * a ^ 2 + 417 * a + 109 := by
  calc
    a ^ 12 = a * a ^ 11 := by ring
    _ = 297 * a ^ 2 + 417 * a + 109 := by
      rw [a_pow_eleven]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_thirteen : a ^ 13 = 417 * a ^ 2 + 1000 * a + 297 := by
  calc
    a ^ 13 = a * a ^ 12 := by ring
    _ = 417 * a ^ 2 + 1000 * a + 297 := by
      rw [a_pow_twelve]
      ring_nf
      rw [a_cubic]
      ring

@[simp] theorem a_pow_fourteen : a ^ 14 = 1000 * a ^ 2 + 1548 * a + 417 := by
  calc
    a ^ 14 = a * a ^ 13 := by ring
    _ = 1000 * a ^ 2 + 1548 * a + 417 := by
      rw [a_pow_thirteen]
      ring_nf
      rw [a_cubic]
      ring

/-- The ramification certificate `3 * (1 - pi^2) = pi^3`. -/
theorem three_mul_one_sub_pi_sq : (3 : L) * (1 - pi ^ 2) = pi ^ 3 := by
  rw [pi_cubed]
  ring

theorem one_sub_pi_sq_ne_zero : (1 : L) - pi ^ 2 ≠ 0 := by
  intro h
  have hpi2 : pi ^ 2 = 1 := (sub_eq_zero.mp h).symm
  have hp3eqpi : pi ^ 3 = pi := by calc
    pi ^ 3 = pi * pi ^ 2 := by ring
    _ = pi := by rw [hpi2, mul_one]
  have hp : pi = 0 := by
    calc
      pi = pi ^ 3 := hp3eqpi.symm
      _ = 3 - 3 * pi ^ 2 := pi_cubed
      _ = 0 := by rw [hpi2]; ring
  rw [hp, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hpi2
  norm_num at hpi2

/-! ## Constant ledger -/

def A0 : L := -a - 1
def q0 : L := a ^ 2 - 1
def rp : L := A0 + q0
def rm : L := A0 - q0
def hp : L := a ^ 2 + 2 * a
def hm : L := a ^ 2 - 2 * a
def mu : L := (a ^ 2 - 2 * a - 2) / 3
def D0 : L := 75 * a ^ 2 + 141 * a + 40
def c0 : L := 12 * (7 * a ^ 2 - 11 * a - 4)
def c2 : L := 60 * (7 * a ^ 2 + 13 * a + 4)
def c3 : L := 24 * D0

local macro "n18_ring" : tactic =>
  `(tactic|
    (ring_nf
     simp only [a_pow_fourteen, a_pow_thirteen, a_pow_twelve, a_pow_eleven,
       a_pow_ten, a_pow_nine,
       a_pow_eight, a_pow_seven, a_pow_six, a_pow_five, a_pow_four, a_cubic]
     ring))

@[simp] theorem q0_sq : q0 ^ 2 = A0 ^ 2 - a := by
  unfold q0 A0
  n18_ring

@[simp] theorem q0_cube : q0 ^ 3 = 3 * a * (a + 1) := by
  unfold q0
  n18_ring

@[simp] theorem rp_sub_rm : rp - rm = 2 * q0 := by
  unfold rp rm
  ring

@[simp] theorem hp_sq : hp ^ 2 = 7 * a ^ 2 + 13 * a + 4 := by
  unfold hp
  n18_ring

@[simp] theorem hm_sq : hm ^ 2 = 7 * a ^ 2 - 11 * a - 4 := by
  unfold hm
  n18_ring

@[simp] theorem mu_sq : mu ^ 2 = (a ^ 2 - a) / 3 := by
  unfold mu
  field_simp
  n18_ring

@[simp] theorem hm_mul_hp : hm * hp = -3 * mu ^ 2 := by
  rw [mu_sq]
  unfold hm hp
  field_simp
  n18_ring

@[simp] theorem hp_cube : hp ^ 3 = -3 * hm * D0 := by
  unfold hp hm D0
  n18_ring

theorem c0_eq : c0 = 12 * hm ^ 2 := by
  rw [hm_sq]
  rfl

theorem c2_eq : c2 = 60 * hp ^ 2 := by
  rw [hp_sq]
  rfl

theorem c0_mul_c3_sq : c0 * c3 ^ 2 = 768 * hp ^ 6 := by
  unfold c0 c3 D0 hp
  n18_ring

theorem c0_mul_c2 : c0 * c2 = 6480 * mu ^ 4 := by
  unfold c0 c2 mu
  field_simp
  n18_ring

theorem c0_sq_mul_c3 : c0 ^ 2 * c3 = 31104 * mu ^ 6 := by
  unfold c0 c3 D0 mu
  field_simp
  n18_ring

/-! ## The sextic and its involution -/

def curveF (x : L) : L :=
  x ^ 6 + 4 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 + 5 * x ^ 2 + 2 * x + 1

def curveFHom (X Z : L) : L :=
  X ^ 6 + 4 * X ^ 5 * Z + 10 * X ^ 4 * Z ^ 2 + 10 * X ^ 3 * Z ^ 3 +
    5 * X ^ 2 * Z ^ 4 + 2 * X * Z ^ 5 + Z ^ 6

def sigmaXNum (X Z : L) : L := A0 * X - a * Z
def sigmaXDen (X Z : L) : L := X - A0 * Z

/-- The Möbius matrix of `sigma` squares to `q0^2 I`. -/
theorem sigma_matrix_sq_00 : A0 * A0 - a = q0 ^ 2 := by
  rw [q0_sq]
  ring

theorem sigma_matrix_sq_01 : A0 * (-a) + (-a) * (-A0) = 0 := by ring

theorem sigma_matrix_sq_10 : A0 + (-A0) = 0 := by ring

/-- Denominator-cleared preservation of the genus-two equation. -/
theorem sigma_preserves_homogeneous (X Z : L) :
    curveFHom (sigmaXNum X Z) (sigmaXDen X Z) = q0 ^ 6 * curveFHom X Z := by
  unfold curveFHom sigmaXNum sigmaXDen A0 q0
  n18_ring

/-- The master even-sextic identity behind both elliptic quotients. -/
theorem quotient_master (z : L) :
    curveFHom (rp - rm * z) (1 - z) = c0 + c2 * z ^ 4 + c3 * z ^ 6 := by
  unfold curveFHom rp rm A0 q0 c0 c2 c3 D0
  n18_ring

/-! ## Exact elliptic-model certificates -/

def E0 : WeierstrassCurve L where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := -5
  a₆ := 5

def Ehat0 : WeierstrassCurve L where
  a₁ := -3
  a₂ := 0
  a₃ := 2
  a₄ := 30
  a₆ := 26

def plusX (x : L) : L := 16 * hp ^ 2 * x - 24 * hp ^ 2
def plusY (x y : L) : L := 32 * hp ^ 3 * (2 * y + x + 1)

theorem plus_model_identity (x y : L) :
    plusY x y ^ 2 - plusX x ^ 3 - c2 * plusX x ^ 2 - c0 * c3 ^ 2 =
      (4 * hp) ^ 6 * (y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + 5 * x - 5) := by
  unfold plusX plusY hp c0 c2 c3 D0
  n18_ring

def minusX (x : L) : L := 16 * mu ^ 2 * x + 12 * mu ^ 2
def minusY (x y : L) : L := 64 * mu ^ 3 * y - 96 * mu ^ 3 * x + 64 * mu ^ 3

theorem minus_model_identity (x y : L) :
    minusY x y ^ 2 - minusX x ^ 3 - c0 * c2 * minusX x - c0 ^ 2 * c3 =
      (4 * mu) ^ 6 * (y ^ 2 - 3 * x * y + 2 * y - x ^ 3 - 30 * x - 26) := by
  unfold minusX minusY mu c0 c2 c3 D0
  field_simp
  n18_ring

/-! ## The rational three-isogeny ring certificate -/

def veluC (u : ℚ) : ℚ := u ^ 3 - 6 * u + 4
def veluA (u : ℚ) : ℚ := u ^ 3 + 6 * u - 8
def veluB (u : ℚ) : ℚ := -18 * u ^ 2 + 24 * u - 8
def veluN (u w : ℚ) : ℚ := veluA u * w + veluB u

theorem velu_identity (u w : ℚ) :
    veluN u w ^ 2 - 3 * u * veluC u * veluN u w + 2 * u ^ 3 * veluN u w -
        veluC u ^ 3 - 30 * u ^ 4 * veluC u - 26 * u ^ 6 =
      veluA u ^ 2 * (w ^ 2 - 3 * u * w + 2 * w - u ^ 3) := by
  unfold veluN veluA veluB veluC
  ring

/-! ## The good model at `pi` -/

def E0Good : WeierstrassCurve L where
  a₁ := a ^ 2 - 2
  a₂ := -a ^ 2 + 2 * a + 1
  a₃ := a + 1
  a₄ := -a ^ 2 + 1
  a₆ := 4 * a ^ 2 - 7 * a - 3

def goodDiscUnit : L := 94 * a ^ 2 - 143 * a - 61

theorem goodDiscUnit_mul_inverse :
    goodDiscUnit * (-325 * a ^ 2 + 113 * a + 936) = 1 := by
  unfold goodDiscUnit
  n18_ring

theorem goodDiscUnit_ne_zero : goodDiscUnit ≠ 0 := by
  intro h
  have := goodDiscUnit_mul_inverse
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- The local model has discriminant `-8` times a `pi`-adic unit. -/
theorem E0Good_delta : E0Good.Δ = (-8 : L) * goodDiscUnit := by
  simp only [E0Good, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  unfold goodDiscUnit
  n18_ring

instance E0Good_isElliptic : E0Good.IsElliptic where
  isUnit := by
    rw [E0Good_delta]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) goodDiscUnit_ne_zero)

/-! ## Small finite certificates used later -/

/-- The reduction of the good model at `pi` has seven points over `F_3`. -/
def reducedGoodCurve : WeierstrassCurve (ZMod 3) where
  a₁ := 2
  a₂ := 2
  a₃ := 2
  a₄ := 0
  a₆ := 0

def reducedGoodAffine (x y : ZMod 3) : Bool :=
  y ^ 2 + 2 * x * y + 2 * y == x ^ 3 + 2 * x ^ 2

theorem reducedGood_affine_count :
    ((Finset.univ : Finset (ZMod 3 × ZMod 3)).filter
      (fun p ↦ reducedGoodAffine p.1 p.2)).card = 6 := by
  decide

end

end MazurProof.N18RouteC
