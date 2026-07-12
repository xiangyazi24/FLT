import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.QuotientGroup.Basic

open Polynomial
open scoped Polynomial nonZeroDivisors
open Ideal hiding map_mul
open FractionalIdeal (coeIdeal_mul)

namespace N18RouteCReference

universe u

variable (K : Type u) [Field K] [DecidableEq K] [CharZero K]

/-- The fixed sextic defining `X_1(18)`. -/
noncomputable def n18F : K[X] :=
  X ^ 6 + 4 * X ^ 5 + 10 * X ^ 4 + 10 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1

/-- The outer polynomial variable is the hyperelliptic `y`-coordinate. -/
noncomputable def n18Rel : K[X][X] := X ^ 2 - C (n18F K)

/-- Affine coordinate ring `K[x,y]/(y^2-f(x))`. -/
abbrev N18AffineRing := AdjoinRoot (n18Rel K)

/-- Function field of the affine coordinate ring. -/
abbrev N18FunctionField := FractionRing (N18AffineRing K)

/-- This is strictly weaker than proving the affine ring Dedekind.
For the fixed squarefree sextic it follows from irreducibility of `Y^2-f`. -/
noncomputable instance n18AffineRingIsDomain : IsDomain (N18AffineRing K) := by
  sorry

/-- Coefficient embedding `K[x] -> A`. -/
noncomputable def coeff : K[X] →+* N18AffineRing K :=
  algebraMap K[X] (N18AffineRing K)

/-- The class of `y` in the quotient ring. -/
noncomputable def yCoord : N18AffineRing K :=
  AdjoinRoot.root (n18Rel K)

/-- The only coordinate-ring relation needed by the ideal calculation. -/
lemma yCoord_sq : yCoord K ^ 2 = coeff K (n18F K) := by
  -- API-level proof: reduce `AdjoinRoot.root` by `n18Rel`.
  sorry

/-- Centered balanced Mumford data.  The identity is `(1,0,0)`.
The `k` coordinate records the difference of the two points at infinity. -/
structure N18Mumford where
  u : K[X]
  v : K[X]
  k : ℤ
  u_monic : u.Monic
  u_natDegree : u.natDegree ≤ 2
  v_mod_u : v % u = v
  curve_dvd : u ∣ v ^ 2 - n18F K

namespace N18Mumford

/-- The distinguished identity representative. -/
noncomputable def identity : N18Mumford K where
  u := 1
  v := 0
  k := 0
  u_monic := monic_one
  u_natDegree := by simp
  v_mod_u := by simp
  curve_dvd := by simp

variable {K}

/-- A chosen quotient in `v^2-f = u*q`. -/
noncomputable def quotient (D : N18Mumford K) : K[X] :=
  Classical.choose D.curve_dvd

lemma quotient_spec (D : N18Mumford K) :
    D.v ^ 2 - n18F K = D.u * D.quotient :=
  Classical.choose_spec D.curve_dvd

/-- Complementary quotient `w=(f-v^2)/u`. -/
noncomputable def complementary (D : N18Mumford K) : K[X] :=
  -D.quotient

lemma complementary_spec (D : N18Mumford K) :
    n18F K - D.v ^ 2 = D.u * D.complementary := by
  rw [complementary]
  calc
    n18F K - D.v ^ 2 = -(D.v ^ 2 - n18F K) := by ring
    _ = -(D.u * D.quotient) := by rw [quotient_spec]
    _ = D.u * -D.quotient := by ring

/-- The Bézout certificate needed for the reverse ideal inclusion.
It follows from squarefreeness of `n18F` and `2 != 0`: a common factor of
`u`, `2v`, and `(f-v^2)/u` would occur twice in `f`. -/
theorem exists_bezout (D : N18Mumford K) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * D.v) + c * D.complementary = 1 := by
  -- Polynomial gcd/xgcd proof; isolated from the ring computation below.
  sorry

end N18Mumford

/-! ## The load-bearing two-generator ideal computation -/

/-- Abstract ring lemma used for the Mumford ideal.  This contains the complete
reverse-inclusion certificate; no Dedekind-domain theorem is involved. -/
lemma span_pair_mul_conj_eq_span
    {R : Type*} [CommRing R]
    (U V W Y a b c : R)
    (hrel : (Y - V) * (Y + V) = U * W)
    (hbez : a * U + b * (2 * V) + c * W = 1) :
    Ideal.span {U, Y - V} * Ideal.span {U, Y + V} = Ideal.span {U} := by
  rw [Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hU : U ∈ Ideal.span ({U} : Set R) :=
      Ideal.subset_span (Set.mem_singleton U)
    rcases hz with rfl | rfl | rfl | rfl
    · exact (Ideal.span {U}).mul_mem_left U hU
    · exact (Ideal.span {U}).mul_mem_right (Y + V) hU
    · exact (Ideal.span {U}).mul_mem_left (Y - V) hU
    · rw [hrel]
      exact (Ideal.span {U}).mul_mem_right W hU
  · rw [Ideal.span_singleton_le_iff_mem]
    let J : Ideal R :=
      Ideal.span {U * U, U * (Y + V), (Y - V) * U, (Y - V) * (Y + V)}
    change U ∈ J
    have hUU : U * U ∈ J := Ideal.subset_span (by simp)
    have hUp : U * (Y + V) ∈ J := Ideal.subset_span (by simp)
    have hUm : (Y - V) * U ∈ J := Ideal.subset_span (by simp)
    have hLast : (Y - V) * (Y + V) ∈ J := Ideal.subset_span (by simp)
    have hU2V : U * (2 * V) ∈ J := by
      have h := J.sub_mem hUp hUm
      convert h using 1 <;> ring
    have hUW : U * W ∈ J := by
      rw [← hrel]
      exact hLast
    have hsum :
        a * (U * U) + b * (U * (2 * V)) + c * (U * W) ∈ J :=
      J.add_mem (J.add_mem (J.mul_mem_left a hUU) (J.mul_mem_left b hU2V))
        (J.mul_mem_left c hUW)
    have heq : a * (U * U) + b * (U * (2 * V)) + c * (U * W) = U := by
      calc
        a * (U * U) + b * (U * (2 * V)) + c * (U * W) =
            U * (a * U + b * (2 * V) + c * W) := by ring
        _ = U := by rw [hbez, mul_one]
    rw [← heq]
    exact hsum

/-- Integral Mumford ideal `<u, y-v>`. -/
noncomputable def mumfordIdeal (D : N18Mumford K) : Ideal (N18AffineRing K) :=
  Ideal.span {coeff K D.u, yCoord K - coeff K D.v}

/-- Conjugate ideal `<u, y+v>`. -/
noncomputable def mumfordConjugateIdeal (D : N18Mumford K) : Ideal (N18AffineRing K) :=
  Ideal.span {coeff K D.u, yCoord K + coeff K D.v}

/-- The relation `(y-v)(y+v)=u*w` inside the coordinate ring. -/
lemma y_sub_mul_y_add (D : N18Mumford K) :
    (yCoord K - coeff K D.v) * (yCoord K + coeff K D.v) =
      coeff K D.u * coeff K D.complementary := by
  calc
    (yCoord K - coeff K D.v) * (yCoord K + coeff K D.v) =
        yCoord K ^ 2 - (coeff K D.v) ^ 2 := by ring
    _ = coeff K (n18F K) - coeff K (D.v ^ 2) := by
      rw [yCoord_sq]
      simp
    _ = coeff K (n18F K - D.v ^ 2) := by simp
    _ = coeff K (D.u * D.complementary) := by
      rw [D.complementary_spec]
    _ = coeff K D.u * coeff K D.complementary := by simp

/-- Map the polynomial Bézout certificate into the coordinate ring. -/
lemma exists_mapped_bezout (D : N18Mumford K) :
    ∃ a b c : N18AffineRing K,
      a * coeff K D.u + b * (2 * coeff K D.v) + c * coeff K D.complementary = 1 := by
  rcases D.exists_bezout with ⟨a, b, c, h⟩
  refine ⟨coeff K a, coeff K b, coeff K c, ?_⟩
  have hm := congrArg (fun p : K[X] => coeff K p) h
  simpa only [map_add, map_mul, map_ofNat, map_one] using hm

/-- Exact integral-ideal identity `I(u,v) * I(u,-v) = (u)`. -/
theorem mumfordIdeal_mul_conjugateIdeal (D : N18Mumford K) :
    mumfordIdeal K D * mumfordConjugateIdeal K D = Ideal.span {coeff K D.u} := by
  rcases exists_mapped_bezout K D with ⟨a, b, c, hbez⟩
  exact span_pair_mul_conj_eq_span
    (coeff K D.u) (coeff K D.v) (coeff K D.complementary) (yCoord K)
    a b c (y_sub_mul_y_add K D) hbez

/-- Monicity of `u` and injectivity of `K[x] -> A` imply this. -/
lemma coeff_u_ne_zero (D : N18Mumford K) : coeff K D.u ≠ 0 := by
  -- Small `AdjoinRoot` API lemma; no Dedekind argument.
  sorry

/-- Group of invertible fractional ideals of the affine ring. -/
abbrev N18InvFrac :=
  (FractionalIdeal (N18AffineRing K)⁰ (N18FunctionField K))ˣ

/-- Directly constructed invertible fractional ideal whose value is `I(u,v)`.
Its inverse is `(1/u) * <u,y+v>`. -/
noncomputable def mumfordUnit (D : N18Mumford K) : N18InvFrac K :=
  Units.mkOfMulEqOne (mumfordIdeal K D)
    (mumfordConjugateIdeal K D *
      (Ideal.span {coeff K D.u} :
        FractionalIdeal (N18AffineRing K)⁰ (N18FunctionField K))⁻¹) <| by
    rw [← mul_assoc, ← coeIdeal_mul, mumfordIdeal_mul_conjugateIdeal,
      FractionalIdeal.coe_ideal_span_singleton_mul_inv (N18FunctionField K)
        (coeff_u_ne_zero K D)]

@[simp]
lemma mumfordUnit_val (D : N18Mumford K) :
    (mumfordUnit K D :
      FractionalIdeal (N18AffineRing K)⁰ (N18FunctionField K)) = mumfordIdeal K D :=
  rfl

/-- The ordinary affine ideal class.  It deliberately forgets `D.k`. -/
noncomputable def finiteClass (D : N18Mumford K) : ClassGroup (N18AffineRing K) :=
  ClassGroup.mk (N18FunctionField K) (mumfordUnit K D)

/-! ## Correct oriented class group

A naïve `ClassGroup A × Z` is not correct: quotienting the first coordinate by
principal ideals before pairing it with the infinity valuation loses the graph
relation.  The orientation is retained in the raw group and only then quotiented.
-/

/-- Raw pair: invertible affine fractional ideal plus an infinity counter. -/
abbrev N18OrientedRaw := N18InvFrac K × Multiplicative ℤ

/-- A valuation at the chosen infinity point, written multiplicatively. -/
abbrev N18InfinityOrder :=
  (N18FunctionField K)ˣ →* Multiplicative ℤ

/-- Principal graph `z |-> ((z), ord_inf(z))`. -/
noncomputable def principalOriented (ordInf : N18InfinityOrder K) :
    (N18FunctionField K)ˣ →* N18OrientedRaw K :=
  (toPrincipalIdeal (N18AffineRing K) (N18FunctionField K)).prod ordInf

/-- Oriented affine class group; this is the projective degree-zero target. -/
abbrev N18OrientedClassGroup (ordInf : N18InfinityOrder K) :=
  N18OrientedRaw K ⧸ (principalOriented K ordInf).range

/-- Additive presentation used for Jacobian arithmetic. -/
abbrev N18PicZero (ordInf : N18InfinityOrder K) :=
  Additive (N18OrientedClassGroup K ordInf)

/-- Raw oriented representative attached to a Mumford triple. -/
noncomputable def orientedRawOf (D : N18Mumford K) : N18OrientedRaw K :=
  (mumfordUnit K D, Multiplicative.ofAdd D.k)

/-- The actual class map. -/
noncomputable def classOf (ordInf : N18InfinityOrder K) (D : N18Mumford K) :
    N18PicZero K ordInf :=
  QuotientGroup.mk' (principalOriented K ordInf).range (orientedRawOf K D)

/-- The identity triple maps to zero. -/
@[simp]
theorem classOf_identity (ordInf : N18InfinityOrder K) :
    classOf K ordInf (N18Mumford.identity K) = 0 := by
  -- Unfold `mumfordUnit`; `I(1,0)=A`, and the counter is zero.
  sorry

/-- Deep reduced-divisor uniqueness in the exact principal-multiplier form
needed by quotient injectivity.  This is the one Riemann--Roch/minimal-pole step. -/
theorem reduced_unique_of_principal
    (ordInf : N18InfinityOrder K)
    (D E : N18Mumford K)
    (z : (N18FunctionField K)ˣ)
    (h : orientedRawOf K D * principalOriented K ordInf z = orientedRawOf K E) :
    D = E := by
  -- Show a multiplier between two degree-<=2 reduced divisors is constant;
  -- contract ideals to recover monic `u`, then recover `v mod u`, then `k`.
  sorry

/-- Injectivity is formal once `reduced_unique_of_principal` is available. -/
theorem classOf_injective (ordInf : N18InfinityOrder K) :
    Function.Injective (classOf K ordInf) := by
  -- Unfold equality in the quotient, obtain a principal graph element,
  -- then apply `reduced_unique_of_principal`.
  sorry

/-- Every oriented degree-zero class has one balanced reduced representative. -/
theorem existsUnique_reduced (ordInf : N18InfinityOrder K)
    (c : N18PicZero K ordInf) :
    ∃! D : N18Mumford K, classOf K ordInf D = c := by
  -- Cantor reduction plus balancing at the two infinity points.
  sorry

/-- Canonical reduced representative of an oriented class. -/
noncomputable def normalize (ordInf : N18InfinityOrder K)
    (c : N18PicZero K ordInf) : N18Mumford K :=
  Classical.choose (existsUnique_reduced K ordInf c)

@[simp]
theorem classOf_normalize (ordInf : N18InfinityOrder K)
    (c : N18PicZero K ordInf) :
    classOf K ordInf (normalize K ordInf c) = c :=
  (Classical.choose_spec (existsUnique_reduced K ordInf c)).1

/-- Addition defined by multiplying oriented classes and normalizing.  A concrete
Cantor implementation is later proved equal to this operation. -/
noncomputable def mumfordAdd (ordInf : N18InfinityOrder K)
    (D E : N18Mumford K) : N18Mumford K :=
  normalize K ordInf (classOf K ordInf D + classOf K ordInf E)

/-- Negation by inversion in the oriented class group followed by normalization. -/
noncomputable def mumfordNeg (ordInf : N18InfinityOrder K)
    (D : N18Mumford K) : N18Mumford K :=
  normalize K ordInf (-classOf K ordInf D)

@[simp]
theorem classOf_mumfordAdd (ordInf : N18InfinityOrder K) (D E : N18Mumford K) :
    classOf K ordInf (mumfordAdd K ordInf D E) =
      classOf K ordInf D + classOf K ordInf E := by
  simp [mumfordAdd]

@[simp]
theorem classOf_mumfordNeg (ordInf : N18InfinityOrder K) (D : N18Mumford K) :
    classOf K ordInf (mumfordNeg K ordInf D) = -classOf K ordInf D := by
  simp [mumfordNeg]

/-- Associativity is inherited from the oriented class group, not proved by
expanding Cantor's formulas. -/
theorem mumfordAdd_assoc (ordInf : N18InfinityOrder K) (D E F : N18Mumford K) :
    mumfordAdd K ordInf (mumfordAdd K ordInf D E) F =
      mumfordAdd K ordInf D (mumfordAdd K ordInf E F) := by
  apply classOf_injective K ordInf
  rw [classOf_mumfordAdd, classOf_mumfordAdd, classOf_mumfordAdd, classOf_mumfordAdd]
  exact add_assoc _ _ _

/-- Commutativity is inherited in the same way. -/
theorem mumfordAdd_comm (ordInf : N18InfinityOrder K) (D E : N18Mumford K) :
    mumfordAdd K ordInf D E = mumfordAdd K ordInf E D := by
  apply classOf_injective K ordInf
  rw [classOf_mumfordAdd, classOf_mumfordAdd]
  exact add_comm _ _

/-- Left identity, with the concrete representative `(1,0,0)`. -/
theorem mumford_identity_add (ordInf : N18InfinityOrder K) (D : N18Mumford K) :
    mumfordAdd K ordInf (N18Mumford.identity K) D = D := by
  apply classOf_injective K ordInf
  rw [classOf_mumfordAdd, classOf_identity, zero_add]

/-- Additive inverse law. -/
theorem mumford_neg_add (ordInf : N18InfinityOrder K) (D : N18Mumford K) :
    mumfordAdd K ordInf (mumfordNeg K ordInf D) D = N18Mumford.identity K := by
  apply classOf_injective K ordInf
  rw [classOf_mumfordAdd, classOf_mumfordNeg, neg_add_cancel, classOf_identity]

/-- A concrete Cantor implementation may replace this definition.  Its only
public proof obligation is the class-level specification below. -/
noncomputable def cantor (ordInf : N18InfinityOrder K)
    (D E : N18Mumford K) : N18Mumford K :=
  mumfordAdd K ordInf D E

@[simp]
theorem classOf_cantor (ordInf : N18InfinityOrder K) (D E : N18Mumford K) :
    classOf K ordInf (cantor K ordInf D E) =
      classOf K ordInf D + classOf K ordInf E := by
  simp [cantor]

/-- Any executable Cantor routine satisfying `classOf_cantor` equals the
transported operation by injectivity. -/
theorem cantor_eq_mumfordAdd (ordInf : N18InfinityOrder K) (D E : N18Mumford K) :
    cantor K ordInf D E = mumfordAdd K ordInf D E :=
  rfl

end N18RouteCReference
