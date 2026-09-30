import FLT.Assumptions.MazurProof.N13ArithmeticBasics
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

open MazurProof.N13Arithmetic

namespace MazurProof.N13Arithmetic

/-- All four affine pairs over F₂ satisfy the generalized equation.
The finite universal quantifiers are checked by ordinary `decide`. -/
theorem optEquation13_zmod2_all :
    ∀ u v : ZMod 2, OptEquation13 u v := by
  change ∀ u v : ZMod 2,
    v ^ 2 + (u ^ 3 + u ^ 2 + 1) * v = u ^ 2 + u
  decide

/-- Forgetting the equation proof loses no affine points over F₂. -/
def affineC2Equiv :
    {uv : ZMod 2 × ZMod 2 // OptEquation13 uv.1 uv.2} ≃
      (ZMod 2 × ZMod 2) where
  toFun := Subtype.val
  invFun uv := ⟨uv, optEquation13_zmod2_all uv.1 uv.2⟩
  left_inv P := by
    apply Subtype.ext
    rfl
  right_inv uv := rfl

/-- The characteristic-two point type from the implementation contract. -/
abbrev C2 := OptPoint13 (ZMod 2)

/-- The four affine pairs and the two infinity tags, without identifying
any affine point or either infinity tag with another point. -/
def c2EquivPairsAndInfinity :
    C2 ≃ ((ZMod 2 × ZMod 2) ⊕ Bool) :=
  Equiv.sumCongr affineC2Equiv (Equiv.refl Bool)

/-- C01: the generalized projective point model has six F₂-points. -/
theorem card_C2 : Nat.card (OptPoint13 (ZMod 2)) = 6 := by
  calc
    Nat.card (OptPoint13 (ZMod 2)) = Nat.card ((ZMod 2 × ZMod 2) ⊕ Bool) :=
      Nat.card_congr c2EquivPairsAndInfinity
    _ = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide

/-! ## Characteristic three (F₃) -/

/-- Characteristic-three optimized points. -/
abbrev C3 := OptPoint13 (ZMod 3)

/-- The affine part of C3. -/
abbrev C3Affine :=
  {uv : ZMod 3 × ZMod 3 // OptEquation13 uv.1 uv.2}

instance : DecidablePred (fun uv : ZMod 3 × ZMod 3 => OptEquation13 uv.1 uv.2) :=
  fun uv => by unfold OptEquation13; infer_instance

instance : Fintype C3Affine := Subtype.fintype _

instance : Fintype C3 := inferInstanceAs (Fintype (C3Affine ⊕ Bool))

/-! ## The six concrete F₃-points -/

def c3A : C3 :=
  Sum.inl ⟨(0, 0), by norm_num [OptEquation13]⟩

def c3B : C3 :=
  Sum.inl ⟨(0, -1), by norm_num [OptEquation13]⟩

def c3C : C3 :=
  Sum.inl ⟨(-1, 0), by norm_num [OptEquation13]⟩

def c3D : C3 :=
  Sum.inl ⟨(-1, -1), by norm_num [OptEquation13]⟩

/-- Small infinity branch, v/u^3 = 0. -/
def c3O : C3 := Sum.inr false

/-- Large infinity branch, v/u^3 = -1. -/
def c3T : C3 := Sum.inr true

/-- Point-level affine enumeration retained for the later reduction argument. -/
theorem C3Affine_cases (P : C3Affine) :
    P.1 = (0, 0) ∨
      P.1 = (0, -1) ∨
      P.1 = (-1, 0) ∨
      P.1 = (-1, -1) := by
  rcases P with ⟨⟨u, v⟩, h⟩
  fin_cases u <;> fin_cases v <;>
    simp [OptEquation13] at h ⊢ <;>
    (try { contradiction }) <;>
    (try { tauto })

/-- Full six-point enumeration, in the cusp order [O,T,D,A,B,C] used by
the Q8470 interface contract. -/
theorem C3_cases (P : C3) :
    P = c3O ∨
      P = c3T ∨
      P = c3D ∨
      P = c3A ∨
      P = c3B ∨
      P = c3C := by
  rcases P with P | b
  · rcases P with ⟨⟨u, v⟩, h⟩
    fin_cases u <;> fin_cases v <;>
      simp [OptEquation13, c3O, c3T, c3D, c3A, c3B, c3C] at h ⊢ <;>
      (try { contradiction }) <;>
      (try { tauto })
  · fin_cases b <;>
      simp [c3O, c3T]

/-- The affine optimized F₃-locus has four points.  This uses ordinary
kernel reduction via `decide`, not `native_decide`. -/
private theorem card_C3Affine :
    Fintype.card C3Affine = 4 := by
  decide

/-- C03: the optimized characteristic-three projective carrier has six
points: four affine points and two infinity branches. -/
theorem card_C3 : Nat.card C3 = 6 := by
  rw [Nat.card_eq_fintype_card]
  show Fintype.card (C3Affine ⊕ Bool) = 6
  rw [Fintype.card_sum, card_C3Affine]
  rfl

/-! ## Characteristic four (F₄) -/

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open scoped CharTwo

/-- Points over the actual four-element Galois field. -/
abbrev C4 := OptPoint13 (GaloisField 2 2)

/-- Over a characteristic-two field satisfying `x^4 = x`, the only
solutions of the optimized affine equation have both coordinates in
`{0, 1}`. This applies to both the two- and four-element fields. -/
theorem optEquation13_iff_of_pow_four
    {K : Type*} [Field K] [CharP K 2]
    (hfour : ∀ x : K, x ^ 4 = x) (u v : K) :
    OptEquation13 u v ↔
      (u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1) := by
  classical
  constructor
  · intro h
    have hu : u = 0 ∨ u = 1 := by
      by_cases hu0 : u = 0
      · exact Or.inl hu0
      right
      by_contra hu1
      have hu3 : u ^ 3 = 1 := by
        apply mul_left_cancel₀ hu0
        calc
          u * u ^ 3 = u ^ 4 := by ring
          _ = u := hfour u
          _ = u * 1 := (mul_one u).symm
      have hfactor : (u - 1) * (u ^ 2 + u + 1) = 0 := by
        calc
          (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
          _ = 0 := by rw [hu3, sub_self]
      have hquad : u ^ 2 + u + 1 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hu1)
      have hrhs : u ^ 2 + u = 1 :=
        CharTwo.add_eq_zero.mp hquad
      have hcoef : u ^ 3 + u ^ 2 + 1 = u ^ 2 := by
        rw [hu3, add_comm (1 : K) (u ^ 2), CharTwo.add_cancel_right]
      have hv : v ^ 2 + u ^ 2 * v = 1 := by
        simpa only [OptEquation13, hcoef, hrhs] using h
      have hsquare : v + u * v ^ 2 = 1 := by
        calc
          v + u * v ^ 2 = v ^ 4 + u ^ 4 * v ^ 2 := by
            rw [hfour v, hfour u]
          _ = (v ^ 2 + u ^ 2 * v) ^ 2 := by
            rw [CharTwo.add_sq, mul_pow, ← pow_mul, ← pow_mul]
          _ = 1 := by rw [hv, one_pow]
      have hmul : u * v ^ 2 + v = u := by
        calc
          u * v ^ 2 + v = u * v ^ 2 + u ^ 3 * v := by
            rw [hu3, one_mul]
          _ = u * (v ^ 2 + u ^ 2 * v) := by ring
          _ = u := by rw [hv, mul_one]
      apply hu1
      calc
        u = u * v ^ 2 + v := hmul.symm
        _ = v + u * v ^ 2 := add_comm _ _
        _ = 1 := hsquare
    have hv : v ^ 2 + v = 0 := by
      rcases hu with rfl | rfl <;>
        simpa [OptEquation13] using h
    have hprod : v * (v - 1) = 0 := by
      calc
        v * (v - 1) = v ^ 2 + v := by
          rw [CharTwo.sub_eq_add]
          ring
        _ = 0 := hv
    refine ⟨hu, ?_⟩
    rcases mul_eq_zero.mp hprod with hv0 | hv1
    · exact Or.inl hv0
    · exact Or.inr (sub_eq_zero.mp hv1)
  · rintro ⟨hu, hv⟩
    rcases hu with rfl | rfl <;>
      rcases hv with rfl | rfl <;>
        simp [OptEquation13]

/-- The two prime-field coordinates, without an arbitrary enumeration
of the ambient finite field. -/
private def q8497bit (K : Type*) [Zero K] [One K] : Bool → K
  | false => 0
  | true => 1

private theorem q8497bit_injective
    (K : Type*) [Field K] : Function.Injective (q8497bit K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [q8497bit]

/-- The four affine points, indexed by two Boolean coordinates. -/
private def q8497affineOfBits
    {K : Type*} [Field K] [CharP K 2]
    (b : Bool × Bool) :
    {uv : K × K // OptEquation13 uv.1 uv.2} := by
  refine ⟨(q8497bit K b.1, q8497bit K b.2), ?_⟩
  rcases b with ⟨a, b⟩
  cases a <;> cases b <;> simp [q8497bit, OptEquation13]

private theorem q8497affineOfBits_bijective
    {K : Type*} [Field K] [CharP K 2]
    (hfour : ∀ x : K, x ^ 4 = x) :
    Function.Bijective (q8497affineOfBits (K := K)) := by
  constructor
  · intro a b h
    apply Prod.ext
    · apply q8497bit_injective K
      exact congrArg
        (fun P : {uv : K × K // OptEquation13 uv.1 uv.2} => P.1.1) h
    · apply q8497bit_injective K
      exact congrArg
        (fun P : {uv : K × K // OptEquation13 uv.1 uv.2} => P.1.2) h
  · rintro ⟨⟨u, v⟩, h⟩
    obtain ⟨hu, hv⟩ := (optEquation13_iff_of_pow_four hfour u v).mp h
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨(false, false), rfl⟩
    · exact ⟨(false, true), rfl⟩
    · exact ⟨(true, false), rfl⟩
    · exact ⟨(true, true), rfl⟩

/-- Four affine points and two infinity points, counted by a proved
bijection rather than by evaluating a noncomputable finite-field model. -/
theorem card_optPoint13_of_pow_four
    {K : Type*} [Field K] [CharP K 2]
    (hfour : ∀ x : K, x ^ 4 = x) :
    Nat.card (OptPoint13 K) = 6 := by
  classical
  let e : (Bool × Bool) ≃
      {uv : K × K // OptEquation13 uv.1 uv.2} :=
    Equiv.ofBijective (q8497affineOfBits (K := K))
      (q8497affineOfBits_bijective hfour)
  let e' : ((Bool × Bool) ⊕ Bool) ≃ OptPoint13 K :=
    Equiv.sumCongr e (Equiv.refl Bool)
  calc
    Nat.card (OptPoint13 K) = Nat.card ((Bool × Bool) ⊕ Bool) :=
      Nat.card_congr e'.symm
    _ = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide

/-- C02: the optimized projective model has six points over `F₄`. -/
theorem card_C4 : Nat.card C4 = 6 := by
  classical
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    simpa [Nat.card_eq_fintype_card] using
      (GaloisField.card 2 2 (by decide))
  have hfour : ∀ x : GaloisField 2 2, x ^ 4 = x := by
    intro x
    simpa only [hcard] using (FiniteField.pow_card x)
  exact card_optPoint13_of_pow_four hfour

end MazurProof.N13Arithmetic
