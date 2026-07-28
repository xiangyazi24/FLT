import FLT.Assumptions.MazurProof.N13GoodModelTwo
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/

open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

namespace MazurProof.N13GoodCoordinateRingTwo

noncomputable section

abbrev K := N13GoodModelTwo.F2

/-- The coefficient of `Y` in polynomial form. -/
def hPoly : K[X] :=
  X ^ 3 + X + 1

/-- The right-hand side in polynomial form. -/
def rhsPoly : K[X] :=
  X ^ 5 + X ^ 4

/-- The outer variable is `Y`, with coefficients in `F₂[X]`. -/
def curvePoly : K[X][X] :=
  X ^ 2 + C hPoly * X - C rhsPoly

theorem hPoly_monic : hPoly.Monic := by
  unfold hPoly
  (monicity; norm_num)

theorem hPoly_natDegree : hPoly.natDegree = 3 := by
  unfold hPoly
  (compute_degree; norm_num)

theorem rhsPoly_monic : rhsPoly.Monic := by
  unfold rhsPoly
  monicity <;> norm_num

theorem rhsPoly_natDegree : rhsPoly.natDegree = 5 := by
  unfold rhsPoly
  compute_degree <;> norm_num

theorem curvePoly_monic : curvePoly.Monic := by
  unfold curvePoly
  monicity <;> norm_num

theorem curvePoly_natDegree : curvePoly.natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num

private theorem zmod_two_nonzero_eq_one (z : K) (hz : z ≠ 0) :
    z = 1 := by
  simpa [K] using ZMod.pow_card_sub_one_eq_one hz

private theorem artinSchreier_degree_le_three
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    q.natDegree ≤ 3 := by
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have : (rhsPoly : K[X]) = 0 := by simpa using heq.symm
    exact rhsPoly_monic.ne_zero this
  by_contra hdeg
  have h4 : 4 ≤ q.natDegree := by omega
  have hlt :
      (hPoly * q).natDegree < (q ^ 2).natDegree := by
    rw [natDegree_mul hPoly_monic.ne_zero hq0, hPoly_natDegree,
      natDegree_pow]
    omega
  have hsum :
      (q ^ 2 + hPoly * q).natDegree = (q ^ 2).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  rw [heq, rhsPoly_natDegree, natDegree_pow] at hsum
  omega

private theorem artinSchreier_reduce_degree
    (q : K[X])
    (heq : q ^ 2 + hPoly * q = rhsPoly) :
    ∃ r : K[X],
      r.natDegree ≤ 2 ∧
      r ^ 2 + hPoly * r = rhsPoly := by
  have hdeg := artinSchreier_degree_le_three q heq
  by_cases hq3 : q.natDegree = 3
  · have hq0 : q ≠ 0 := by
      intro hq
      subst q
      norm_num at hq3
    have hlead : q.leadingCoeff = 1 :=
      zmod_two_nonzero_eq_one q.leadingCoeff
        (leadingCoeff_ne_zero.mpr hq0)
    have hqMonic : q.Monic := hlead
    have hqDegree : IsMonicOfDegree q 3 := ⟨hq3, hqMonic⟩
    have hhDegree : IsMonicOfDegree hPoly 3 :=
      ⟨hPoly_natDegree, hPoly_monic⟩
    refine ⟨q - hPoly, ?_, ?_⟩
    · have hlt :
          (q - hPoly).natDegree < 3 :=
        hqDegree.natDegree_sub_lt (n := 3) (by norm_num) hhDegree
      omega
    · have htwo : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      calc
        (q - hPoly) ^ 2 + hPoly * (q - hPoly) =
            q ^ 2 + hPoly * q - 2 * (q * hPoly) := by ring
        _ = q ^ 2 + hPoly * q := by rw [htwo, zero_mul, sub_zero]
        _ = rhsPoly := heq
  · refine ⟨q, ?_, heq⟩
    omega

private theorem no_artinSchreier_polynomial_root
    (q : K[X]) :
    q ^ 2 + hPoly * q ≠ rhsPoly := by
  intro heq
  obtain ⟨r, hrdeg, hre⟩ := artinSchreier_reduce_degree q heq
  have hr :
      r =
        C (r.coeff 2) * X ^ 2 +
          C (r.coeff 1) * X +
            C (r.coeff 0) := by
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    by_cases hn2 : n = 2
    · subst n
      simp
    have hn : 2 < n := by omega
    have hrzero : r.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (hrdeg.trans_lt hn)
    have h1n : 1 ≠ n := by omega
    rw [hrzero]
    simp [coeff_X, coeff_C, hn0, h1n, hn2]
  rw [hr] at hre
  simp only [hPoly, rhsPoly] at hre
  ring_nf at hre
  have hcoeffFive :=
    congrArg (fun p : K[X] => p.coeff 5) hre
  have hcoeffTwo :=
    congrArg (fun p : K[X] => p.coeff 2) hre
  have htwoK : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [← C_pow] at hcoeffFive hcoeffTwo
  simp [coeff_add, coeff_C_mul, coeff_mul_C, coeff_X_pow, htwoK] at hcoeffFive hcoeffTwo
  have hbb : r.coeff 1 + r.coeff 1 = 0 := by
    rw [← two_mul, htwoK, zero_mul]
  have hzero : r.coeff 2 = 0 := by
    linear_combination hcoeffTwo - hbb
  rw [hzero] at hcoeffFive
  exact zero_ne_one hcoeffFive

private theorem curvePoly_not_isRoot (q : K[X]) :
    ¬IsRoot curvePoly q := by
  intro hq
  have heq :
      q ^ 2 + hPoly * q = rhsPoly := by
    have hzero :
        q ^ 2 + hPoly * q - rhsPoly = 0 := by
      simpa only [IsRoot.def, curvePoly, eval_sub, eval_add, eval_pow,
        eval_X, eval_C, eval_mul] using hq
    exact sub_eq_zero.mp hzero
  exact no_artinSchreier_polynomial_root q heq

theorem curvePoly_irreducible : Irreducible curvePoly := by
  rw [curvePoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro q hq
    exact curvePoly_not_isRoot q
      ((mem_roots curvePoly_monic.ne_zero).mp hq)
  · norm_num [curvePoly_natDegree]
  · norm_num [curvePoly_natDegree]

instance curvePolyIrreducibleFact : Fact (Irreducible curvePoly) :=
  ⟨curvePoly_irreducible⟩

/-- The affine coordinate ring of the special fibre. -/
abbrev CoordinateRing : Type :=
  AdjoinRoot curvePoly

/-- Its fraction field. -/
abbrev FunctionField : Type :=
  FractionRing CoordinateRing

instance : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime curvePoly_irreducible.prime

noncomputable instance : Algebra K CoordinateRing :=
  inferInstance

noncomputable instance : Algebra K[X] CoordinateRing :=
  inferInstance

/-- Quotient map to the affine coordinate ring. -/
def mk : K[X][X] →+* CoordinateRing :=
  AdjoinRoot.mk curvePoly

/-- Embed a polynomial in the `X` coordinate. -/
def xClass (p : K[X]) : CoordinateRing :=
  mk (C p)

/-- The class of the `Y` coordinate. -/
def yClass : CoordinateRing :=
  mk X

/-- The polynomial-coordinate embedding. -/
def xClassHom : K[X] →+* CoordinateRing :=
  AdjoinRoot.of curvePoly

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom p = xClass p := rfl

@[simp] theorem xClass_zero : xClass 0 = 0 :=
  map_zero xClassHom

@[simp] theorem xClass_one : xClass 1 = 1 :=
  map_one xClassHom

@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n

@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass (p - q) = xClass p - xClass q :=
  map_sub xClassHom p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass (-p) = -xClass p :=
  map_neg xClassHom p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass (p * q) = xClass p * xClass q :=
  map_mul xClassHom p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass (p ^ n) = xClass p ^ n :=
  map_pow xClassHom p n

@[simp] theorem yClass_relation :
    yClass ^ 2 + xClass hPoly * yClass = xClass rhsPoly := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring

theorem xClass_ne_zero {p : K[X]} (hp : p ≠ 0) :
    xClass p ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt curvePoly_monic
    (C_ne_zero.mpr hp) (by rw [curvePoly_natDegree, natDegree_C]; norm_num)

/-! ## Generalized Mumford graph ideals -/

/-- Hyperelliptic conjugation sends a graph value `v` to `-h-v`. -/
def conjugateV (v : K[X]) : K[X] :=
  -hPoly - v

/-- Integral generalized Mumford data, including the Cantor quotient and
the precise smoothness Bézout identity needed for ideal invertibility. -/
structure SemiMumford where
  u : K[X]
  v : K[X]
  w : K[X]
  u_monic : u.Monic
  curve_eq : v ^ 2 + hPoly * v - rhsPoly = u * w
  bezout :
    ∃ a b c : K[X],
      a * u + b * (2 * v + hPoly) + c * w = 1

/-- The graph function `Y-v(X)`. -/
def ySubClass (v : K[X]) : CoordinateRing :=
  yClass - xClass v

/-- The integral graph ideal `(u,Y-v)`. -/
def mumfordIdeal (u v : K[X]) : Ideal CoordinateRing :=
  Ideal.span {xClass u, ySubClass v}

theorem xClass_mem_mumfordIdeal (u v : K[X]) :
    xClass u ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

theorem ySubClass_mem_mumfordIdeal (u v : K[X]) :
    ySubClass v ∈ mumfordIdeal u v :=
  Ideal.subset_span (by simp)

/-- The two graph generators multiply to the negative Cantor quotient. -/
theorem ySubClass_mul_conjugate (D : SemiMumford) :
    ySubClass D.v * ySubClass (conjugateV D.v) =
      -(xClass D.u * xClass D.w) := by
  calc
    ySubClass D.v * ySubClass (conjugateV D.v) =
        yClass ^ 2 + xClass hPoly * yClass -
          (xClass D.v ^ 2 + xClass hPoly * xClass D.v) := by
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub]
      ring
    _ = xClass rhsPoly -
          xClass (D.v ^ 2 + hPoly * D.v) := by
      rw [yClass_relation, xClass_add, xClass_mul, xClass_pow]
    _ = -xClass (D.v ^ 2 + hPoly * D.v - rhsPoly) := by
      rw [xClass_sub]
      ring
    _ = -xClass (D.u * D.w) := by rw [D.curve_eq]
    _ = -(xClass D.u * xClass D.w) := by rw [xClass_mul]

/-- The characteristic-two generalized graph ideal satisfies
`(u,Y-v)(u,Y+h+v)=(u)`. -/
theorem mumfordIdeal_mul_conj_integral (D : SemiMumford) :
    mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) =
      Ideal.span ({xClass D.u} : Set CoordinateRing) := by
  let I := mumfordIdeal D.u D.v
  let J := mumfordIdeal D.u (conjugateV D.v)
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro p hp q hq
    rw [Ideal.mem_span_singleton]
    obtain ⟨p₀, pY, hpEq⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨q₀, qY, hqEq⟩ := Ideal.mem_span_pair.mp hq
    refine ⟨p₀ * q₀ * xClass D.u +
        p₀ * qY * ySubClass (conjugateV D.v) +
        pY * q₀ * ySubClass D.v -
        pY * qY * xClass D.w, ?_⟩
    rw [← hpEq, ← hqEq]
    linear_combination pY * qY * ySubClass_mul_conjugate D
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := D.bezout
    have huI : xClass D.u ∈ I :=
      xClass_mem_mumfordIdeal D.u D.v
    have huJ : xClass D.u ∈ J :=
      xClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hvI : ySubClass D.v ∈ I :=
      ySubClass_mem_mumfordIdeal D.u D.v
    have hvJ : ySubClass (conjugateV D.v) ∈ J :=
      ySubClass_mem_mumfordIdeal D.u (conjugateV D.v)
    have hu2 : xClass D.u * xClass D.u ∈ I * J :=
      Ideal.mul_mem_mul huI huJ
    have huv :
        xClass D.u * xClass (2 * D.v + hPoly) ∈ I * J := by
      have hp :
          xClass D.u * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul huI hvJ
      have hm :
          ySubClass D.v * xClass D.u ∈ I * J :=
        Ideal.mul_mem_mul hvI huJ
      have hd := Ideal.sub_mem (I * J) hp hm
      convert hd using 1
      simp only [ySubClass, conjugateV, xClass_neg, xClass_sub,
        xClass_add, xClass_mul]
      have htwoPoly : (2 : K[X]) = 0 :=
        CharP.cast_eq_zero (K[X]) 2
      have htwoCoord : (2 : CoordinateRing) = 0 := by
        calc
          (2 : CoordinateRing) = xClass (2 : K[X]) :=
            (xClass_natCast 2).symm
          _ = xClass 0 := by rw [htwoPoly]
          _ = 0 := xClass_zero
      rw [htwoPoly, xClass_zero, zero_mul, zero_add]
      have hvadd : xClass D.v + xClass D.v = 0 := by
        rw [← two_mul, htwoCoord, zero_mul]
      calc
        xClass D.u * xClass hPoly =
            xClass D.u * xClass hPoly +
              xClass D.u * (xClass D.v + xClass D.v) := by
          rw [hvadd, mul_zero, add_zero]
        _ = xClass D.u *
              (yClass - (-xClass hPoly - xClass D.v)) -
            (yClass - xClass D.v) * xClass D.u := by ring
    have huw : xClass D.u * xClass D.w ∈ I * J := by
      have hg :
          ySubClass D.v * ySubClass (conjugateV D.v) ∈ I * J :=
        Ideal.mul_mem_mul hvI hvJ
      have hneg := (I * J).neg_mem hg
      rw [ySubClass_mul_conjugate] at hneg
      simpa using hneg
    have ha :
        xClass a * (xClass D.u * xClass D.u) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass a) hu2
    have hb :
        xClass b *
          (xClass D.u * xClass (2 * D.v + hPoly)) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass b) huv
    have hc :
        xClass c * (xClass D.u * xClass D.w) ∈ I * J :=
      Ideal.mul_mem_left (I * J) (xClass c) huw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass a * (xClass D.u * xClass D.u) +
            xClass b *
              (xClass D.u * xClass (2 * D.v + hPoly)) +
            xClass c * (xClass D.u * xClass D.w) =
          xClass D.u := by
      calc
        _ = xClass D.u *
            xClass
              (a * D.u + b * (2 * D.v + hPoly) + c * D.w) := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = xClass D.u * 1 := by rw [hbez, xClass_one]
        _ = xClass D.u := mul_one _
    rw [heq] at hsum
    exact hsum

theorem mumfordIdeal_mul_conj_fractional (D : SemiMumford) :
    (mumfordIdeal D.u D.v :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) =
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField) := by
  rw [← coeIdeal_mul, mumfordIdeal_mul_conj_integral]

/-- Invertible fractional ideals of the special affine coordinate ring. -/
abbrev InvFrac :=
  (FractionalIdeal CoordinateRing⁰ FunctionField)ˣ

/-- A generalized Mumford graph ideal as a unit fractional ideal. -/
def mumfordIdealUnit (D : SemiMumford) : InvFrac :=
  Units.mkOfMulEqOne
    (mumfordIdeal D.u D.v :
      FractionalIdeal CoordinateRing⁰ FunctionField)
    ((mumfordIdeal D.u (conjugateV D.v) :
        FractionalIdeal CoordinateRing⁰ FunctionField) *
      (Ideal.span ({xClass D.u} : Set CoordinateRing) :
        FractionalIdeal CoordinateRing⁰ FunctionField)⁻¹)
    (by
      rw [← mul_assoc, mumfordIdeal_mul_conj_fractional]
      exact FractionalIdeal.coe_ideal_span_singleton_mul_inv
        FunctionField (xClass_ne_zero D.u_monic.ne_zero))

@[simp] theorem coe_mumfordIdealUnit (D : SemiMumford) :
    (mumfordIdealUnit D :
      FractionalIdeal CoordinateRing⁰ FunctionField) =
      mumfordIdeal D.u D.v := rfl

end

end MazurProof.N13GoodCoordinateRingTwo
