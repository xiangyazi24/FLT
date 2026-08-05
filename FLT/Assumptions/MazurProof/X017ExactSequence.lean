import FLT.Assumptions.MazurProof.RationalPointsN15ExactSequence

/-!
# The sharpened two-isogeny exact sequence for `X₀(17)`

The general two-isogeny exact sequence bounds `G / 2G` by the product of two
endpoint quotients.  For the standard `X₀(17)` model, the first arrow is
expected to vanish: the left endpoint has two cosets, represented by zero and
a point killed by the dual isogeny.  Exactness then embeds `G / 2G` into the
right endpoint, improving the bound from four to two.

The second section records the corresponding general rank criterion.  In a
finitely generated abelian group, its torsion subgroup contributes exactly
`|G[2]|` classes modulo doubling.  If the entire quotient has no more classes
than this, the free quotient is trivial.
-/

namespace MazurProof.X017ExactSequence

open MazurProof.RationalPointsN15ExactSequence

universe u v

/-! ## Vanishing of the left exact-sequence map -/

section SharpenedExactSequence

variable {G : Type u} {H : Type v}
variable [AddCommGroup G] [AddCommGroup H]

/-- The quotient `H / φ(G)` has representatives zero and `η`.  This form
retains witnesses in `G`, which lets the isogeny identities reduce both
representatives modulo doubling without choosing a quotient equivalence. -/
def TwoCosetExhaustion (φ : G →+ H) (η : H) : Prop :=
  ∀ h : H, ∃ g : G, h = φ g ∨ h = η + φ g

/-- If the two left-end representatives are zero and a point killed by the
dual map, then the first arrow `H / φ(G) → G / 2G` is identically zero. -/
theorem leftMap_eq_zero_of_twoCosetExhaustion
    (φ : G →+ H) (ψ : H →+ G)
    (hψφ : ∀ g : G, ψ (φ g) = 2 • g)
    (η : H) (hψη : ψ η = 0)
    (hrep : TwoCosetExhaustion φ η) :
    leftMap φ ψ hψφ = 0 := by
  apply AddMonoidHom.ext
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ h =>
      obtain ⟨g, hg | hg⟩ := hrep h
      · rw [hg, leftMap_mk, hψφ]
        exact (QuotientAddGroup.eq_zero_iff (2 • g)).mpr ⟨g, rfl⟩
      · rw [hg, leftMap_mk, map_add, hψη, zero_add, hψφ]
        exact (QuotientAddGroup.eq_zero_iff (2 • g)).mpr ⟨g, rfl⟩

/-- Exactness at `G / 2G` turns a zero left arrow into injectivity of the
right arrow `G / 2G → G / ψ(H)`. -/
theorem rightMap_injective_of_leftMap_eq_zero
    (φ : G →+ H) (ψ : H →+ G)
    (hψφ : ∀ g : G, ψ (φ g) = 2 • g)
    (hzero : leftMap φ ψ hψφ = 0) :
    Function.Injective (rightMap φ ψ hψφ) := by
  intro a b hab
  apply sub_eq_zero.mp
  have habker : a - b ∈ (rightMap φ ψ hψφ).ker := by
    change rightMap φ ψ hψφ (a - b) = 0
    rw [map_sub, hab, sub_self]
  rw [ker_rightMap_eq_range_leftMap] at habker
  rcases habker with ⟨q, hq⟩
  calc
    a - b = leftMap φ ψ hψφ q := hq.symm
    _ = 0 := by rw [hzero]; rfl

/-- When the right endpoint is finite and the first arrow vanishes,
injectivity of the right arrow supplies a finite structure on `G / 2G`. -/
@[implicit_reducible] noncomputable def middleFintype_of_leftMap_eq_zero
    (φ : G →+ H) (ψ : H →+ G)
    (hψφ : ∀ g : G, ψ (φ g) = 2 • g)
    [Fintype (G ⧸ ψ.range)]
    (hzero : leftMap φ ψ hψφ = 0) :
    Fintype (DoubleQuotient G) :=
  Fintype.ofInjective (rightMap φ ψ hψφ)
    (rightMap_injective_of_leftMap_eq_zero φ ψ hψφ hzero)

/-- The sharpened exact sequence bounds `|G / 2G|` by the right endpoint
alone whenever the left arrow vanishes. -/
theorem natCard_doubleQuotient_le_right
    (φ : G →+ H) (ψ : H →+ G)
    (hψφ : ∀ g : G, ψ (φ g) = 2 • g)
    [Fintype (G ⧸ ψ.range)]
    (hzero : leftMap φ ψ hψφ = 0) :
    Nat.card (DoubleQuotient G) ≤ Nat.card (G ⧸ ψ.range) := by
  letI : Fintype (DoubleQuotient G) :=
    middleFintype_of_leftMap_eq_zero φ ψ hψφ hzero
  exact Nat.card_le_card_of_injective
    (rightMap φ ψ hψφ)
    (rightMap_injective_of_leftMap_eq_zero φ ψ hψφ hzero)

end SharpenedExactSequence

/-! ## Rank zero at the exact two-torsion bound -/

section RankCriterion

variable (G : Type u) [AddCommGroup G] [AddGroup.FG G]

/-- If a finitely generated abelian group has no more classes modulo doubling
than rational two-torsion points, its free rank is zero.  The torsion subgroup
injects into `G / 2G` with exactly `|G[2]|` classes, so the assumed inequality
forces this injection to be surjective.  The torsion-free quotient modulo two
is then trivial, which forces the free quotient itself to vanish. -/
theorem freeRank_eq_zero_of_doubleQuotient_le_twoTorsion
    [Finite (DoubleQuotient G)]
    (hDouble :
      Nat.card (DoubleQuotient G) ≤ Nat.card (TwoTorsion G)) :
    AddCommGroup.freeRank G = 0 := by
  letI : Module.Finite ℤ G :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
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
      Nat.card (DoubleQuotient (AddCommGroup.torsion G)) =
        Nat.card (TwoTorsion G) := by
    calc
      Nat.card (DoubleQuotient (AddCommGroup.torsion G)) =
          Nat.card (TwoTorsion (AddCommGroup.torsion G)) :=
        natCard_doubleQuotient_eq_twoTorsion_of_finite _
      _ = Nat.card (TwoTorsion G) :=
        Nat.card_congr (twoTorsionTorsionEquiv G)
  have hTinjective := torsionModTwoMap_injective G
  have hTwoLe :
      Nat.card (TwoTorsion G) ≤ Nat.card (DoubleQuotient G) := by
    rw [← hTcard]
    exact Nat.card_le_card_of_injective
      (torsionModTwoMap G) hTinjective
  have hGcard :
      Nat.card (DoubleQuotient G) = Nat.card (TwoTorsion G) :=
    le_antisymm hDouble hTwoLe
  have hTsurjective : Function.Surjective (torsionModTwoMap G) :=
    (hTinjective.bijective_of_nat_card_le
      (by rw [hGcard, hTcard])).2
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

end MazurProof.X017ExactSequence
