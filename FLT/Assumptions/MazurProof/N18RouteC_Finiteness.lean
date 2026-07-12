import FLT.Assumptions.MazurProof.N18RouteC_Separated

/-!
# MW-finite-generation-free finiteness core for N18 Route C

A group annihilated by `21` splits explicitly into its `3`- and `7`-primary
subgroups.  A finite mod-three quotient controls the first factor, while good
reduction controls the second.  Explicit points of orders three and seven then
identify the group with `ZMod 21`.
-/

namespace MazurProof.N18RouteC.Finiteness

open Function

noncomputable section

section PrimaryDecomposition

variable {G : Type*} [AddCommGroup G]

def nTorsion (n : ℕ) : AddSubgroup G where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change n • x = 0 at hx
    change n • y = 0 at hy
    change n • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    simpa [nsmul_neg, hx]

@[simp] theorem mem_nTorsion {n : ℕ} {x : G} :
    x ∈ nTorsion (G := G) n ↔ n • x = 0 := Iff.rfl

def nsmulHom (n : ℕ) : G →+ G where
  toFun x := n • x
  map_zero' := by simp
  map_add' x y := by simp [nsmul_add]

@[simp] theorem nsmulHom_apply (n : ℕ) (x : G) :
    nsmulHom (G := G) n x = n • x := rfl

def nRange (n : ℕ) : AddSubgroup G :=
  (nsmulHom (G := G) n).range

@[simp] theorem mem_nRange {n : ℕ} {x : G} :
    x ∈ nRange (G := G) n ↔ ∃ y : G, n • y = x := Iff.rfl

abbrev ThreePrimary (G : Type*) [AddCommGroup G] : AddSubgroup G :=
  nTorsion (G := G) 3

abbrev SevenPrimary (G : Type*) [AddCommGroup G] : AddSubgroup G :=
  nTorsion (G := G) 7

abbrev ThreeRange (G : Type*) [AddCommGroup G] : AddSubgroup G :=
  nRange (G := G) 3

abbrev SevenRange (G : Type*) [AddCommGroup G] : AddSubgroup G :=
  nRange (G := G) 7

theorem seven_nsmul_eq_self_of_three_nsmul_eq_zero
    {x : G} (hx : (3 : ℕ) • x = 0) :
    (7 : ℕ) • x = x := by
  calc
    (7 : ℕ) • x = (1 + 2 * 3 : ℕ) • x := by norm_num
    _ = (1 : ℕ) • x + (2 * 3 : ℕ) • x := by rw [add_nsmul]
    _ = x + (3 : ℕ) • ((2 : ℕ) • x) := by rw [one_nsmul, mul_nsmul]
    _ = x + (2 : ℕ) • ((3 : ℕ) • x) := by
      rw [Separated.nsmul_nsmul_comm 3 2 x]
    _ = x := by simp [hx]

theorem fifteen_nsmul_eq_self_of_seven_nsmul_eq_zero
    {x : G} (hx : (7 : ℕ) • x = 0) :
    (15 : ℕ) • x = x := by
  calc
    (15 : ℕ) • x = (1 + 2 * 7 : ℕ) • x := by norm_num
    _ = (1 : ℕ) • x + (2 * 7 : ℕ) • x := by rw [add_nsmul]
    _ = x + (7 : ℕ) • ((2 : ℕ) • x) := by rw [one_nsmul, mul_nsmul]
    _ = x + (2 : ℕ) • ((7 : ℕ) • x) := by
      rw [Separated.nsmul_nsmul_comm 7 2 x]
    _ = x := by simp [hx]

theorem fifteen_nsmul_eq_zero_of_three_nsmul_eq_zero
    {x : G} (hx : (3 : ℕ) • x = 0) :
    (15 : ℕ) • x = 0 := by
  calc
    (15 : ℕ) • x = (5 : ℕ) • ((3 : ℕ) • x) := by
      rw [← mul_nsmul]
    _ = 0 := by simp [hx]

def primaryDecomposition
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    G ≃+ ThreePrimary G × SevenPrimary G where
  toFun x :=
    (⟨(7 : ℕ) • x, by
        change (3 : ℕ) • ((7 : ℕ) • x) = 0
        calc
          (3 : ℕ) • ((7 : ℕ) • x) = (21 : ℕ) • x := by
            rw [← mul_nsmul]
          _ = 0 := h21 x⟩,
     ⟨(15 : ℕ) • x, by
        change (7 : ℕ) • ((15 : ℕ) • x) = 0
        calc
          (7 : ℕ) • ((15 : ℕ) • x) = (5 : ℕ) • ((21 : ℕ) • x) := by
            simp only [← mul_nsmul]
          _ = 0 := by simp [h21 x]⟩)
  invFun p := (p.1 : G) + (p.2 : G)
  left_inv x := by
    change (7 : ℕ) • x + (15 : ℕ) • x = x
    calc
      (7 : ℕ) • x + (15 : ℕ) • x = (22 : ℕ) • x := by
        rw [← add_nsmul]
      _ = (1 + 21 : ℕ) • x := by norm_num
      _ = x := by rw [add_nsmul, one_nsmul, h21 x, add_zero]
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext
    · apply Subtype.ext
      change (7 : ℕ) • ((a : G) + (b : G)) = (a : G)
      rw [nsmul_add,
        seven_nsmul_eq_self_of_three_nsmul_eq_zero a.property,
        b.property, add_zero]
    · apply Subtype.ext
      change (15 : ℕ) • ((a : G) + (b : G)) = (b : G)
      rw [nsmul_add,
        fifteen_nsmul_eq_zero_of_three_nsmul_eq_zero a.property,
        fifteen_nsmul_eq_self_of_seven_nsmul_eq_zero b.property,
        zero_add]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp [nsmul_add]
    · apply Subtype.ext
      simp [nsmul_add]

theorem sevenRange_eq_threePrimary
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    SevenRange G = ThreePrimary G := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (3 : ℕ) • ((7 : ℕ) • y) = 0
    calc
      (3 : ℕ) • ((7 : ℕ) • y) = (21 : ℕ) • y := by
        rw [← mul_nsmul]
      _ = 0 := h21 y
  · intro hx
    refine ⟨x, ?_⟩
    exact seven_nsmul_eq_self_of_three_nsmul_eq_zero hx

theorem threeRange_eq_sevenPrimary
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    ThreeRange G = SevenPrimary G := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (7 : ℕ) • ((3 : ℕ) • y) = 0
    calc
      (7 : ℕ) • ((3 : ℕ) • y) = (21 : ℕ) • y := by
        rw [← mul_nsmul]
      _ = 0 := h21 y
  · intro hx
    refine ⟨(5 : ℕ) • x, ?_⟩
    calc
      (3 : ℕ) • ((5 : ℕ) • x) = (15 : ℕ) • x := by
        rw [← mul_nsmul]
      _ = x := fifteen_nsmul_eq_self_of_seven_nsmul_eq_zero hx

theorem threePrimary_inf_sevenPrimary_eq_bot :
    ThreePrimary G ⊓ SevenPrimary G = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [AddSubgroup.mem_bot]
    have h3 : (3 : ℕ) • (x : G) = 0 := hx.1
    have h7 : (7 : ℕ) • (x : G) = 0 := hx.2
    exact (seven_nsmul_eq_self_of_three_nsmul_eq_zero h3).symm.trans h7
  · exact bot_le

end PrimaryDecomposition

section ModThree

variable {G : Type*} [AddCommGroup G]

def projThree
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    G →+ ThreePrimary G where
  toFun x :=
    ⟨(7 : ℕ) • x, by
      change (3 : ℕ) • ((7 : ℕ) • x) = 0
      calc
        (3 : ℕ) • ((7 : ℕ) • x) = (21 : ℕ) • x := by
          rw [← mul_nsmul]
        _ = 0 := h21 x⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [nsmul_add]

theorem projThree_surjective
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    Function.Surjective (projThree h21) := by
  intro a
  refine ⟨(a : G), ?_⟩
  apply Subtype.ext
  exact seven_nsmul_eq_self_of_three_nsmul_eq_zero a.property

theorem ker_projThree_eq_threeRange
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    (projThree h21).ker = ThreeRange G := by
  calc
    (projThree h21).ker = SevenPrimary G := by
      ext x
      simp [projThree, SevenPrimary, nTorsion]
    _ = ThreeRange G := (threeRange_eq_sevenPrimary h21).symm

def modThreeEquivThreePrimary
    (h21 : ∀ x : G, (21 : ℕ) • x = 0) :
    G ⧸ ThreeRange G ≃+ ThreePrimary G :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (ker_projThree_eq_threeRange h21).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (projThree h21) (projThree_surjective h21))

theorem finite_threePrimary_of_finite_modThree
    (h21 : ∀ x : G, (21 : ℕ) • x = 0)
    [Finite (G ⧸ ThreeRange G)] :
    Finite (ThreePrimary G) := by
  let e := modThreeEquivThreePrimary h21
  exact Finite.of_injective e.symm e.symm.injective

theorem natCard_le_of_injective
    {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (hf : Function.Injective f) :
    Nat.card α ≤ Nat.card β := by
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective f hf

theorem card_threePrimary_le
    (h21 : ∀ x : G, (21 : ℕ) • x = 0)
    [Finite (G ⧸ ThreeRange G)]
    (hmod3 : Nat.card (G ⧸ ThreeRange G) ≤ 3) :
    Nat.card (ThreePrimary G) ≤ 3 := by
  calc
    Nat.card (ThreePrimary G) = Nat.card (G ⧸ ThreeRange G) :=
      (Nat.card_congr (modThreeEquivThreePrimary h21).toEquiv).symm
    _ ≤ 3 := hmod3

end ModThree

section Reduction

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

def redOnSeven (red : G →+ A) : SevenPrimary G →+ A :=
  red.comp (SevenPrimary G).subtype

theorem redOnSeven_injective
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0) :
    Function.Injective (redOnSeven red) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  apply hker7 (x : G) x.property
  simpa [redOnSeven] using hx

theorem finite_sevenPrimary_of_reduction
    [Finite A]
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0) :
    Finite (SevenPrimary G) :=
  Finite.of_injective (redOnSeven red)
    (redOnSeven_injective red hker7)

theorem card_sevenPrimary_le
    [Finite A]
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0)
    (hA : Nat.card A = 7) :
    Nat.card (SevenPrimary G) ≤ 7 := by
  letI : Finite (SevenPrimary G) :=
    finite_sevenPrimary_of_reduction red hker7
  calc
    Nat.card (SevenPrimary G) ≤ Nat.card A :=
      natCard_le_of_injective (redOnSeven red)
        (redOnSeven_injective red hker7)
    _ = 7 := hA

end Reduction

section FiniteAssembly

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

theorem finite_of_modThree_and_reduction
    (h21 : ∀ x : G, (21 : ℕ) • x = 0)
    [Finite (G ⧸ ThreeRange G)]
    [Finite A]
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0) :
    Finite G := by
  letI : Finite (ThreePrimary G) :=
    finite_threePrimary_of_finite_modThree h21
  letI : Finite (SevenPrimary G) :=
    finite_sevenPrimary_of_reduction red hker7
  exact Finite.of_injective (primaryDecomposition h21)
    (primaryDecomposition h21).injective

theorem card_le_twentyOne
    (h21 : ∀ x : G, (21 : ℕ) • x = 0)
    [Finite (G ⧸ ThreeRange G)]
    [Finite A]
    (hmod3 : Nat.card (G ⧸ ThreeRange G) ≤ 3)
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0)
    (hA : Nat.card A = 7) :
    Nat.card G ≤ 21 := by
  letI : Finite (ThreePrimary G) :=
    finite_threePrimary_of_finite_modThree h21
  letI : Finite (SevenPrimary G) :=
    finite_sevenPrimary_of_reduction red hker7
  letI : Finite G := finite_of_modThree_and_reduction h21 red hker7
  calc
    Nat.card G = Nat.card (ThreePrimary G × SevenPrimary G) :=
      Nat.card_congr (primaryDecomposition h21).toEquiv
    _ = Nat.card (ThreePrimary G) * Nat.card (SevenPrimary G) := by simp
    _ ≤ 3 * 7 := Nat.mul_le_mul
      (card_threePrimary_le h21 hmod3)
      (card_sevenPrimary_le red hker7 hA)
    _ = 21 := by norm_num

end FiniteAssembly

section CyclicTwentyOne

variable {G : Type*} [AddCommGroup G]

theorem addOrderOf_add_eq_twentyOne
    {T3 T7 : G}
    (h3 : addOrderOf T3 = 3)
    (h7 : addOrderOf T7 = 7) :
    addOrderOf (T3 + T7) = 21 := by
  have hcop : (addOrderOf T3).Coprime (addOrderOf T7) := by
    rw [h3, h7]
    norm_num
  simpa [h3, h7] using
    (AddCommute.all T3 T7).addOrderOf_add_eq_mul_addOrderOf_of_coprime
      hcop

def zmodGeneratorHom
    {n : ℕ} (T : G) (hT : addOrderOf T = n) :
    ZMod n →+ G where
  toFun k := (ZMod.cast k : ℤ) • T
  map_zero' := by simp
  map_add' x y := by
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
    rw [← Int.cast_add]
    simp only [ZMod.coe_intCast, ← hT,
      mod_addOrderOf_zsmul, add_zsmul]

theorem zmodGeneratorHom_injective
    {n : ℕ} (T : G) (hT : addOrderOf T = n) :
    Function.Injective (zmodGeneratorHom T hT) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have ha : a • T = 0 := by
    simpa [zmodGeneratorHom, ZMod.coe_intCast, ← hT,
      mod_addOrderOf_zsmul] using hx
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← hT]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := T) (i := a)).2 ha

def zmodTwentyOneEquivOfCard
    [Finite G]
    (T : G)
    (hT : addOrderOf T = 21)
    (hcard : Nat.card G = 21) :
    ZMod 21 ≃+ G := by
  letI : Fintype G := Fintype.ofFinite G
  apply AddEquiv.ofBijective (zmodGeneratorHom T hT)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨zmodGeneratorHom_injective T hT, ?_⟩
  simpa [Nat.card_eq_fintype_card] using hcard.symm

def zmodTwentyOneEquivOfBlock7
    {A : Type*} [AddCommGroup A]
    (h21 : ∀ x : G, (21 : ℕ) • x = 0)
    [Finite (G ⧸ ThreeRange G)]
    [Finite A]
    (hmod3 : Nat.card (G ⧸ ThreeRange G) ≤ 3)
    (red : G →+ A)
    (hker7 : ∀ x : G,
      (7 : ℕ) • x = 0 → red x = 0 → x = 0)
    (hA : Nat.card A = 7)
    (T3 T7 : G)
    (h3 : addOrderOf T3 = 3)
    (h7 : addOrderOf T7 = 7) :
    ZMod 21 ≃+ G := by
  letI : Finite G := finite_of_modThree_and_reduction h21 red hker7
  have hT : addOrderOf (T3 + T7) = 21 :=
    addOrderOf_add_eq_twentyOne h3 h7
  have hUpper : Nat.card G ≤ 21 :=
    card_le_twentyOne h21 hmod3 red hker7 hA
  have hLower : 21 ≤ Nat.card G :=
    by
      simpa [Nat.card_zmod] using
        natCard_le_of_injective
          (zmodGeneratorHom (T3 + T7) hT)
          (zmodGeneratorHom_injective (T3 + T7) hT)
  exact zmodTwentyOneEquivOfCard (T3 + T7) hT
    (le_antisymm hUpper hLower)

end CyclicTwentyOne

end


end MazurProof.N18RouteC.Finiteness
