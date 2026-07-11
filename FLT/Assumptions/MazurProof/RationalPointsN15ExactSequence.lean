import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.ModN
import FLT.Assumptions.MazurProof.RationalPointsN15Descent

/-!
# The abstract exact sequence behind the order-15 two-isogeny descent

Mathlib currently has no elliptic-curve isogeny object and no Mordell--Weil
theorem.  This file therefore isolates and proves the entire group-theoretic
part of the descent.  For homomorphisms `φ : G → H` and `ψ : H → G` whose
composites are multiplication by two, it constructs the exact sequence

`H/φG → G/2G → G/ψH`

and proves the corresponding cardinal bound.  It also proves, for a finitely
generated abelian group, that a four-element two-torsion kernel together with
`|G/2G| ≤ 4` forces free rank zero.  Combining both statements gives the
standard two-isogeny rank-zero criterion.

The sole elliptic-curve-specific boundary left by this file is to realize the
explicit affine maps from `RationalPointsN15Descent` as group homomorphisms and
identify their two quotient groups with the already computed squareclass
images.  No such API exists in Mathlib at present.
-/

namespace MazurProof.RationalPointsN15ExactSequence

universe u v

/-! ## Quotients by multiplication by two -/

abbrev doubleRange (G : Type u) [AddCommGroup G] : AddSubgroup G :=
  (nsmulAddMonoidHom (α := G) 2).range

abbrev DoubleQuotient (G : Type u) [AddCommGroup G] : Type u :=
  G ⧸ doubleRange G

abbrev TwoTorsion (G : Type u) [AddCommGroup G] : Type u :=
  {g : G // 2 • g = 0}

section IsogenySequence

variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
variable (φ : G →+ H) (ψ : H →+ G)
variable (hψφ : ∀ g : G, ψ (φ g) = 2 • g)

include φ hψφ in
theorem doubleRange_le_psiRange : doubleRange G ≤ ψ.range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨φ g, hψφ g⟩

include hψφ in
theorem phiRange_le_comap_doubleRange :
    φ.range ≤ AddSubgroup.comap ψ (doubleRange G) := by
  rintro _ ⟨g, rfl⟩
  exact ⟨g, (hψφ g).symm⟩

/-- The first arrow `H/φG → G/2G` in the descent exact sequence. -/
def leftMap : H ⧸ φ.range →+ DoubleQuotient G :=
  QuotientAddGroup.map φ.range (doubleRange G) ψ
    (phiRange_le_comap_doubleRange φ ψ hψφ)

/-- The quotient arrow `G/2G → G/ψH`. -/
def rightMap : DoubleQuotient G →+ G ⧸ ψ.range :=
  QuotientAddGroup.map (doubleRange G) ψ.range (AddMonoidHom.id G)
    (by
      intro g hg
      exact (doubleRange_le_psiRange φ ψ hψφ) hg)

@[simp] theorem leftMap_mk (h : H) :
    leftMap φ ψ hψφ (h : H ⧸ φ.range) =
      (ψ h : DoubleQuotient G) := by
  rfl

@[simp] theorem rightMap_mk (g : G) :
    rightMap φ ψ hψφ (g : DoubleQuotient G) =
      (g : G ⧸ ψ.range) := by
  rfl

/-- Exactness at `G/2G`. -/
theorem ker_rightMap_eq_range_leftMap :
    (rightMap φ ψ hψφ).ker = (leftMap φ ψ hψφ).range := by
  apply le_antisymm
  · rintro q hq
    induction q using QuotientAddGroup.induction_on with
    | _ g =>
      have hgψ : g ∈ ψ.range := by
        apply (QuotientAddGroup.eq_zero_iff g).mp
        simpa using hq
      rcases hgψ with ⟨h, hh⟩
      refine ⟨(h : H ⧸ φ.range), ?_⟩
      rw [leftMap_mk, hh]
  · rintro _ ⟨q, rfl⟩
    induction q using QuotientAddGroup.induction_on with
    | _ h =>
      change (ψ h : G ⧸ ψ.range) = 0
      exact (QuotientAddGroup.eq_zero_iff (ψ h)).mpr ⟨h, rfl⟩

/-- Finite end terms make the middle quotient finite. -/
@[implicit_reducible] noncomputable def middleFintype
    [Fintype (H ⧸ φ.range)] [Fintype (G ⧸ ψ.range)] :
    Fintype (DoubleQuotient G) :=
  AddGroup.fintypeOfKerLeRange (leftMap φ ψ hψφ) (rightMap φ ψ hψφ)
    (ker_rightMap_eq_range_leftMap φ ψ hψφ).le

include hψφ in
/-- Cardinal inequality attached to the exact sequence:
`|G/2G| ≤ |H/φG| |G/ψH|`. -/
theorem natCard_doubleQuotient_le_mul
    [Fintype (H ⧸ φ.range)] [Fintype (G ⧸ ψ.range)] :
    Nat.card (DoubleQuotient G) ≤
      Nat.card (H ⧸ φ.range) * Nat.card (G ⧸ ψ.range) := by
  letI : Fintype (DoubleQuotient G) := middleFintype φ ψ hψφ
  have hker := ker_rightMap_eq_range_leftMap φ ψ hψφ
  have hright : Nat.card (rightMap φ ψ hψφ).range ≤
      Nat.card (G ⧸ ψ.range) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.coe_injective
  have hleft : Nat.card (leftMap φ ψ hψφ).range ≤
      Nat.card (H ⧸ φ.range) :=
    Nat.card_le_card_of_surjective
      (leftMap φ ψ hψφ).rangeRestrict
      (leftMap φ ψ hψφ).rangeRestrict_surjective
  have hquot :
      Nat.card (DoubleQuotient G ⧸ (rightMap φ ψ hψφ).ker) =
        Nat.card (rightMap φ ψ hψφ).range :=
    Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange (rightMap φ ψ hψφ)).toEquiv
  have hkerCard : Nat.card (rightMap φ ψ hψφ).ker =
      Nat.card (leftMap φ ψ hψφ).range := by
    rw [hker]
  calc
    Nat.card (DoubleQuotient G) =
        Nat.card (DoubleQuotient G ⧸ (rightMap φ ψ hψφ).ker) *
          Nat.card (rightMap φ ψ hψφ).ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card (rightMap φ ψ hψφ).range *
          Nat.card (leftMap φ ψ hψφ).range := by
      rw [hquot, hkerCard]
    _ ≤ Nat.card (G ⧸ ψ.range) * Nat.card (H ⧸ φ.range) :=
      Nat.mul_le_mul hright hleft
    _ = Nat.card (H ⧸ φ.range) * Nat.card (G ⧸ ψ.range) :=
      Nat.mul_comm _ _

include hψφ in
theorem natCard_doubleQuotient_le_four
    [Fintype (H ⧸ φ.range)] [Fintype (G ⧸ ψ.range)]
    (hleft : Nat.card (H ⧸ φ.range) ≤ 2)
    (hright : Nat.card (G ⧸ ψ.range) ≤ 2) :
    Nat.card (DoubleQuotient G) ≤ 4 := by
  exact (natCard_doubleQuotient_le_mul φ ψ hψφ).trans
    (by nlinarith)

end IsogenySequence

/-! ## The finite torsion contribution -/

section FiniteGroup

variable (T : Type u) [AddCommGroup T] [Finite T]

/-- For a finite abelian group, the cokernel and kernel of multiplication by
two have the same cardinality. -/
theorem natCard_doubleQuotient_eq_twoTorsion_of_finite :
    Nat.card (DoubleQuotient T) = Nat.card (TwoTorsion T) := by
  let f : T →+ T := nsmulAddMonoidHom (α := T) 2
  have hT_range : Nat.card T = Nat.card (T ⧸ f.range) * Nat.card f.range :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  have hT_ker : Nat.card T = Nat.card (T ⧸ f.ker) * Nat.card f.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have hfirst : Nat.card (T ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hrange_pos : 0 < Nat.card f.range := Nat.card_pos
  change Nat.card (T ⧸ f.range) = Nat.card f.ker
  rw [hfirst] at hT_ker
  nlinarith

end FiniteGroup

/-! ## Separating the torsion and free contributions -/

section TorsionAndFree

variable (G : Type u) [AddCommGroup G]

/-- The map from the mod-two quotient of the torsion subgroup into the
mod-two quotient of the whole group. -/
def torsionModTwoMap :
    DoubleQuotient (AddCommGroup.torsion G) →+ DoubleQuotient G :=
  QuotientAddGroup.map
    (doubleRange (AddCommGroup.torsion G)) (doubleRange G)
    (AddCommGroup.torsion G).subtype (by
      rintro _ ⟨t, rfl⟩
      exact ⟨(t : G), rfl⟩)

@[simp] theorem torsionModTwoMap_mk (t : AddCommGroup.torsion G) :
    torsionModTwoMap G
        (t : DoubleQuotient (AddCommGroup.torsion G)) =
      ((t : G) : DoubleQuotient G) := by
  rfl

/-- Passing from torsion modulo two to the ambient group modulo two loses no
information.  The key point is that if twice an ambient element is torsion,
then that ambient element is already torsion. -/
theorem torsionModTwoMap_injective : Function.Injective (torsionModTwoMap G) := by
  have hker : ∀ q, torsionModTwoMap G q = 0 → q = 0 := by
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | _ t =>
      have htG : (t : G) ∈ doubleRange G := by
        apply (QuotientAddGroup.eq_zero_iff (t : G)).mp
        simpa using hq
      rcases htG with ⟨g, hg⟩
      change 2 • g = (t : G) at hg
      have h2g : IsOfFinAddOrder (2 • g) := by
        rw [hg]
        exact t.property
      rcases isOfFinAddOrder_iff_nsmul_eq_zero.mp h2g with ⟨n, hn, hng⟩
      have hgT : g ∈ AddCommGroup.torsion G := by
        apply (AddCommGroup.mem_torsion g).mpr
        apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
        refine ⟨2 * n, Nat.mul_pos (by decide) hn, ?_⟩
        simpa only [mul_nsmul] using hng
      apply (QuotientAddGroup.eq_zero_iff t).mpr
      refine ⟨⟨g, hgT⟩, ?_⟩
      apply Subtype.ext
      exact hg
  intro a b hab
  apply sub_eq_zero.mp
  apply hker (a - b)
  rw [map_sub, hab, sub_self]

/-- The natural map from `G/2G` onto the mod-two quotient of the torsion-free
quotient `G/G_tors`. -/
def freeModTwoMap :
    DoubleQuotient G →+
      DoubleQuotient (G ⧸ AddCommGroup.torsion G) :=
  QuotientAddGroup.map (doubleRange G)
    (doubleRange (G ⧸ AddCommGroup.torsion G))
    (QuotientAddGroup.mk' (AddCommGroup.torsion G)) (by
      rintro _ ⟨g, rfl⟩
      exact ⟨(g : G ⧸ AddCommGroup.torsion G), rfl⟩)

@[simp] theorem freeModTwoMap_mk (g : G) :
    freeModTwoMap G (g : DoubleQuotient G) =
      ((g : G ⧸ AddCommGroup.torsion G) :
        DoubleQuotient (G ⧸ AddCommGroup.torsion G)) := by
  rfl

theorem freeModTwoMap_surjective : Function.Surjective (freeModTwoMap G) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ q =>
    induction q using QuotientAddGroup.induction_on with
    | _ g => exact ⟨(g : DoubleQuotient G), rfl⟩

/-- The torsion contribution maps to zero in the torsion-free quotient. -/
theorem freeModTwoMap_comp_torsionModTwoMap (q) :
    freeModTwoMap G (torsionModTwoMap G q) = 0 := by
  induction q using QuotientAddGroup.induction_on with
  | _ t =>
    change (((t : G) : G ⧸ AddCommGroup.torsion G) :
      DoubleQuotient (G ⧸ AddCommGroup.torsion G)) = 0
    rw [(QuotientAddGroup.eq_zero_iff (t : G)).mpr t.property]
    rfl

/-- All two-torsion lies in the torsion subgroup, so taking two-torsion before
or after restricting to the torsion subgroup gives equivalent types. -/
def twoTorsionTorsionEquiv :
    TwoTorsion (AddCommGroup.torsion G) ≃ TwoTorsion G where
  toFun t :=
    ⟨(t.1 : G), by
      exact congrArg Subtype.val t.property⟩
  invFun g :=
    ⟨⟨g.1, (AddCommGroup.mem_torsion g.1).mpr <|
      isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by decide, g.2⟩⟩,
      by
        apply Subtype.ext
        exact g.2⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl

end TorsionAndFree

/-! ## The rank-zero criterion -/

section RankCriterion

variable (G : Type u) [AddCommGroup G] [AddGroup.FG G]

/-- In a finitely generated abelian group, if the two-torsion already has four
elements and the quotient modulo doubling has at most four elements, then
there is no free part. -/
theorem freeRank_eq_zero_of_natCard_doubleQuotient_le_four
    [Finite (DoubleQuotient G)]
    (hTwoTorsion : Nat.card (TwoTorsion G) = 4)
    (hDouble : Nat.card (DoubleQuotient G) ≤ 4) :
    AddCommGroup.freeRank G = 0 := by
  letI : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hTfg : (AddCommGroup.torsion G).toIntSubmodule.FG :=
    Submodule.FG.of_le Module.Finite.fg_top le_top
  letI : Module.Finite ℤ (AddCommGroup.torsion G) :=
    Module.Finite.of_fg hTfg
  letI : AddGroup.FG (AddCommGroup.torsion G) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  have hTtorsion : AddMonoid.IsTorsion (AddCommGroup.torsion G) := by
    intro t
    exact (AddCommGroup.torsion G).subtype_injective.isOfFinAddOrder_iff.mp
      t.property
  letI : Finite (AddCommGroup.torsion G) :=
    AddCommGroup.finite_of_fg_torsion _ hTtorsion
  have hTcard :
      Nat.card (DoubleQuotient (AddCommGroup.torsion G)) = 4 := by
    calc
      Nat.card (DoubleQuotient (AddCommGroup.torsion G)) =
          Nat.card (TwoTorsion (AddCommGroup.torsion G)) :=
        natCard_doubleQuotient_eq_twoTorsion_of_finite _
      _ = Nat.card (TwoTorsion G) :=
        Nat.card_congr (twoTorsionTorsionEquiv G)
      _ = 4 := hTwoTorsion
  have hTinjective := torsionModTwoMap_injective G
  have hFourLe : 4 ≤ Nat.card (DoubleQuotient G) := by
    rw [← hTcard]
    exact Nat.card_le_card_of_injective (torsionModTwoMap G) hTinjective
  have hGcard : Nat.card (DoubleQuotient G) = 4 :=
    le_antisymm hDouble hFourLe
  have hTsurjective : Function.Surjective (torsionModTwoMap G) :=
    (hTinjective.bijective_of_nat_card_le (by rw [hGcard, hTcard])).2
  have hFreeMapZero : ∀ q, freeModTwoMap G q = 0 := by
    intro q
    obtain ⟨t, rfl⟩ := hTsurjective q
    exact freeModTwoMap_comp_torsionModTwoMap G t
  have hFreeModTwoSubsingleton :
      Subsingleton
        (DoubleQuotient (G ⧸ AddCommGroup.torsion G)) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := freeModTwoMap_surjective G a
    obtain ⟨b, rfl⟩ := freeModTwoMap_surjective G b
    rw [hFreeMapZero, hFreeMapZero]
  have hFreeModTwoCard :
      Nat.card (DoubleQuotient (G ⧸ AddCommGroup.torsion G)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨hFreeModTwoSubsingleton, inferInstance⟩
  letI : Module.Finite ℤ (G ⧸ AddCommGroup.torsion G) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hPow :
      2 ^ Module.finrank ℤ (G ⧸ AddCommGroup.torsion G) = 1 := by
    calc
      2 ^ Module.finrank ℤ (G ⧸ AddCommGroup.torsion G) =
          (doubleRange (G ⧸ AddCommGroup.torsion G)).index :=
        (AddSubgroup.index_range_nsmul
          (G ⧸ AddCommGroup.torsion G) 2).symm
      _ = Nat.card
          (DoubleQuotient (G ⧸ AddCommGroup.torsion G)) :=
        AddSubgroup.index_eq_card _
      _ = 1 := hFreeModTwoCard
  have hFinrank :
      Module.finrank ℤ (G ⧸ AddCommGroup.torsion G) = 0 := by
    simpa using hPow
  have hFreeSubsingleton :
      Subsingleton (G ⧸ AddCommGroup.torsion G) :=
    (Module.finrank_eq_zero_iff_of_free
      ℤ (G ⧸ AddCommGroup.torsion G)).mp hFinrank
  apply AddCommGroup.freeRank_eq_zero_iff.mpr
  apply AddCommGroup.torsion_eq_top_iff.mp
  exact QuotientAddGroup.subsingleton_iff.mp hFreeSubsingleton

end RankCriterion

/-! ## The consumable two-isogeny criterion -/

/-- A directly consumable rank-zero criterion for a two-isogeny descent.
The geometric layer supplies the two group homomorphisms, the doubling
identity, the two endpoint squareclass bounds, and the size of rational
two-torsion; everything after those inputs is proved in this file. -/
theorem freeRank_eq_zero_of_twoIsogeny
    {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
    [AddGroup.FG G]
    (φ : G →+ H) (ψ : H →+ G)
    (hψφ : ∀ g : G, ψ (φ g) = 2 • g)
    [Fintype (H ⧸ φ.range)] [Fintype (G ⧸ ψ.range)]
    (hLeft : Nat.card (H ⧸ φ.range) ≤ 2)
    (hRight : Nat.card (G ⧸ ψ.range) ≤ 2)
    (hTwoTorsion : Nat.card (TwoTorsion G) = 4) :
    AddCommGroup.freeRank G = 0 := by
  letI : Fintype (DoubleQuotient G) := middleFintype φ ψ hψφ
  apply freeRank_eq_zero_of_natCard_doubleQuotient_le_four G hTwoTorsion
  exact natCard_doubleQuotient_le_four φ ψ hψφ hLeft hRight

end MazurProof.RationalPointsN15ExactSequence
