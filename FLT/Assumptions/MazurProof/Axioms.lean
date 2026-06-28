import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.TorsionFinite
import FLT.Assumptions.MazurProof.TwoInvariantFactors

/-!
# Axioms for the Mazur torsion-bound proof scaffold

This file collects the hard mathematical inputs needed to prove the numerical
bound `|E(ℚ)_tors| ≤ 16`.  The axioms are grouped by expected discharge
priority.
-/

open scoped WeierstrassCurve.Affine
open scoped DirectSum
open scoped Function
open Polynomial

namespace MazurProof

/-- The torsion subgroup of `E(ℚ)`, as a set, matching `FLT/Assumptions/Mazur.lean`. -/
abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- Placeholder for "all `m`-torsion points of `E` are rational". -/
def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for "there is a rational point of exact order `n` on `E`". -/
def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/--
Placeholder for the structure-theorem assertion
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`.
-/
def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for `E(ℚ)_tors` containing a subgroup `ℤ/2ℤ × ℤ/nℤ`. -/
abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

/--
Finite two-invariant-factor data for the rational torsion subgroup.

The `has_point_order_n` field records the evident element of order `n` in
`ℤ/mℤ × ℤ/nℤ`; it is kept as part of the axiom so the later arithmetic input
can be used without developing finite abelian group theory here.
-/
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

/-! ## Group A: torsion structure, expected easiest to discharge -/

/-! ## Group B: Weil pairing -/

/--
Weil pairing consequence: if all `m`-torsion points are rational, then `ℚ`
contains a primitive `m`-th root of unity.
-/
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

private abbrev AffinePoint (W : WeierstrassCurve ℚ) :=
  WeierstrassCurve.Affine.Point W

private noncomputable def twoTorsionCubic (W : WeierstrassCurve ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

private lemma twoTorsionCubic_eval (W : WeierstrassCurve ℚ) (x : ℚ) :
    (twoTorsionCubic W).eval x =
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionCubic]

private lemma twoTorsionCubic_ne_zero (W : WeierstrassCurve ℚ) :
    twoTorsionCubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℚ[X] => p.coeff 3) h
  norm_num [twoTorsionCubic] at hcoeff

private lemma twoTorsionCubic_natDegree_le (W : WeierstrassCurve ℚ) :
    (twoTorsionCubic W).natDegree ≤ 3 := by
  simpa [twoTorsionCubic] using
    (Polynomial.natDegree_cubic_le (a := (4 : ℚ)) (b := W.b₂)
      (c := 2 * W.b₄) (d := W.b₆))

private lemma affine_two_torsion_y_eq_negY
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    y = WeierstrassCurve.Affine.negY W x y := by
  by_contra hy
  have hs : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some _ _
        (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
  rw [h2] at hs
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hs.symm

private lemma affine_two_torsion_linear_relation
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    2 * y + W.a₁ * x + W.a₃ = 0 := by
  have hy := affine_two_torsion_y_eq_negY (W := W) h2
  rw [WeierstrassCurve.Affine.negY] at hy
  linear_combination hy

private lemma affine_two_torsion_cubic
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y : ℚ}
    {h : WeierstrassCurve.Affine.Nonsingular W x y}
    (h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    (twoTorsionCubic W).eval x = 0 := by
  rw [twoTorsionCubic_eval]
  have heq : WeierstrassCurve.Affine.Equation W x y := h.1
  have hrel := affine_two_torsion_linear_relation (W := W) h2
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  nlinarith

private lemma affine_two_torsion_same_x
    {W : WeierstrassCurve ℚ} [W.IsElliptic] {x y₁ y₂ : ℚ}
    {h₁ : WeierstrassCurve.Affine.Nonsingular W x y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular W x y₂}
    (ht₁ : (WeierstrassCurve.Affine.Point.some x y₁ h₁ : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y₁ h₁ = 0)
    (ht₂ : (WeierstrassCurve.Affine.Point.some x y₂ h₂ : AffinePoint W) +
        WeierstrassCurve.Affine.Point.some x y₂ h₂ = 0) :
    (WeierstrassCurve.Affine.Point.some x y₁ h₁ : AffinePoint W) =
      WeierstrassCurve.Affine.Point.some x y₂ h₂ := by
  have hr₁ := affine_two_torsion_linear_relation (W := W) ht₁
  have hr₂ := affine_two_torsion_linear_relation (W := W) ht₂
  have hy : y₁ = y₂ := by nlinarith
  subst hy
  rfl

private abbrev TwoTorsionPoint (W : WeierstrassCurve ℚ) [W.IsElliptic] :=
  {P : AffinePoint W // P + P = 0}

private noncomputable def encodeTwoTorsion (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : TwoTorsionPoint W) : Option ((twoTorsionCubic W).rootSet ℚ) :=
  match hP : P.1 with
  | 0 => none
  | WeierstrassCurve.Affine.Point.some x y h =>
      some ⟨x, by
        have h2 : (WeierstrassCurve.Affine.Point.some x y h : AffinePoint W) +
            WeierstrassCurve.Affine.Point.some x y h = 0 := by
          simpa [hP] using P.2
        have hroot := affine_two_torsion_cubic (W := W) (x := x) (y := y) (h := h) h2
        rw [Polynomial.mem_rootSet_of_ne (twoTorsionCubic_ne_zero W)]
        simpa [IsRoot, aeval_def] using hroot⟩

private theorem encodeTwoTorsion_injective (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Function.Injective (encodeTwoTorsion W) := by
  rintro ⟨P, hP2⟩ ⟨Q, hQ2⟩ henc
  apply Subtype.ext
  change P = Q
  cases P with
  | zero =>
      cases Q with
      | zero =>
          rfl
      | some x₂ y₂ h₂ =>
          simp [encodeTwoTorsion] at henc
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          simp [encodeTwoTorsion] at henc
      | some x₂ y₂ h₂ =>
          have hx : x₁ = x₂ := by
            simp [encodeTwoTorsion] at henc
            exact henc
          subst x₂
          have ht₁ : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : AffinePoint W) +
              WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ = 0 := by
            exact hP2
          have ht₂ : (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ : AffinePoint W) +
              WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ = 0 := by
            exact hQ2
          exact affine_two_torsion_same_x (W := W) (x := x₁) (y₁ := y₁) (y₂ := y₂)
            (h₁ := h₁) (h₂ := h₂) ht₁ ht₂

private noncomputable instance twoTorsionPoint_fintype
    (W : WeierstrassCurve ℚ) [W.IsElliptic] : Fintype (TwoTorsionPoint W) :=
  Fintype.ofInjective (encodeTwoTorsion W) (encodeTwoTorsion_injective W)

private theorem card_twoTorsionPoint_le_four (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    Fintype.card (TwoTorsionPoint W) ≤ 4 := by
  classical
  have hencode :
      Fintype.card (TwoTorsionPoint W) ≤
        Fintype.card (Option ((twoTorsionCubic W).rootSet ℚ)) :=
    Fintype.card_le_of_injective (encodeTwoTorsion W) (encodeTwoTorsion_injective W)
  have hroots :
      Fintype.card ((twoTorsionCubic W).rootSet ℚ) ≤ 3 := by
    rw [Set.fintypeCard_eq_ncard]
    exact (Polynomial.ncard_rootSet_le (twoTorsionCubic W) ℚ).trans
      (twoTorsionCubic_natDegree_le W)
  calc
    Fintype.card (TwoTorsionPoint W)
        ≤ Fintype.card (Option ((twoTorsionCubic W).rootSet ℚ)) := hencode
    _ = Fintype.card ((twoTorsionCubic W).rootSet ℚ) + 1 := by simp
    _ ≤ 4 := by omega

private abbrev ZMod2Cube :=
  ZMod 2 × ZMod 2 × ZMod 2

private lemma two_nsmul_zmod2cube (g : ZMod2Cube) : (2 : ℕ) • g = 0 := by
  ext <;> exact ZModModule.char_nsmul_eq_zero 2 _

private theorem no_zmod2cube_injective_to_elliptic_point
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ¬ ∃ f : ZMod2Cube →+ AffinePoint W, Function.Injective f := by
  rintro ⟨f, hf⟩
  let toTwoTorsion : ZMod2Cube → TwoTorsionPoint W := fun g =>
    ⟨f g, by
      have htwo : (2 : ℕ) • f g = 0 := by
        rw [← f.map_nsmul, two_nsmul_zmod2cube]
        simp
      simpa [two_nsmul] using htwo⟩
  have hto_inj : Function.Injective toTwoTorsion := by
    intro a b h
    apply hf
    exact congrArg Subtype.val h
  have hcard :
      Fintype.card ZMod2Cube ≤ Fintype.card (TwoTorsionPoint W) :=
    Fintype.card_le_of_injective toTwoTorsion hto_inj
  have hdomain : Fintype.card ZMod2Cube = 8 := by
    simp [ZMod2Cube, Fintype.card_prod, ZMod.card]
  have hcodomain : Fintype.card (TwoTorsionPoint W) ≤ 4 :=
    card_twoTorsionPoint_le_four W
  omega

private theorem no_zmod2cube_injective_to_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod2Cube →+ (AddCommGroup.torsion (E⁄ℚ).Point),
        Function.Injective f := by
  rintro ⟨f, hf⟩
  let incl : (AddCommGroup.torsion (E⁄ℚ).Point) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  exact no_zmod2cube_injective_to_elliptic_point E ⟨incl.comp f, hincl.comp hf⟩

private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    ¬ ∃ f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E⁄ℚ).Point),
        Function.Injective f := by
  rintro ⟨f, hf⟩
  let incl : (AddCommGroup.torsion (E⁄ℚ).Point) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p :=
    ⟨incl.comp f, hincl.comp hf⟩
  rcases weil_pairing_primitive_root E hp.pos hfull with ⟨ζ, hζ⟩
  have hle : p ≤ 2 := isPrimitiveRoot_rat_order_le_two hζ
  omega

/--
The rational torsion subgroup has two invariant factors:
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`, and cardinality `m * n`.
-/
noncomputable def rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E := by
  classical
  let G := AddCommGroup.torsion (E⁄ℚ).Point
  have hfin := rational_torsion_finite_alias E
  haveI : Finite G := hfin.to_subtype
  let d : TwoInvariantFactorData' G :=
    Classical.choose
      (finite_abelian_two_invariant_factors_exists' G
        (no_odd_prime_square_in_torsion E)
        (no_zmod2cube_injective_to_torsion E))
  let incl : G →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  refine
    { m := d.m
      n := d.n
      m_pos := d.m_pos
      n_pos := d.n_pos
      dvd_mn := d.dvd_mn
      has_structure := ?_
      has_point_order_n := ?_
      card_eq := ?_ }
  · rcases d.equiv with ⟨e⟩
    exact ⟨incl.comp e.symm.toAddMonoidHom, hincl.comp e.symm.injective⟩
  · rcases d.order_n with ⟨x, hx⟩
    exact ⟨(x : (E⁄ℚ).Point), by
      rw [← hx]
      exact AddSubgroup.addOrderOf_coe x⟩
  · rw [← d.card_eq]
    rfl

/--
If the first invariant factor of the rational torsion subgroup is `m`, then
the full `m`-torsion is rational.
-/
theorem first_invariant_factor_full_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hstruct : HasTorsionStructure E m n) :
    HasFullRationalTorsion E m := by
  obtain ⟨embed, hembed⟩ := zmod_prod_contains_square m n hm hn hmn
  obtain ⟨f, hf⟩ := hstruct
  exact ⟨f.comp embed, hf.comp hembed⟩

/-! ## Group C: noncyclic exclusions -/

/-- No elliptic curve over `ℚ` has rational torsion containing `ℤ/2ℤ × ℤ/nℤ`
for `n ∈ {10, 12, 14, 16}`. -/
theorem no_Z2_cross_Z14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 14 :=
  no_Z2_cross_Z14_from_descent E

theorem no_Z2_cross_Z16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 16 :=
  no_Z2_cross_Z16_from_descent E

theorem no_Z2_cross_Zn_forbidden
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16) :
    ¬ ContainsZ2xZn E n := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact no_Z2_cross_Z10 E
  · exact no_Z2_cross_Z12 E
  · exact no_Z2_cross_Z14 E
  · exact no_Z2_cross_Z16 E

/-! ## Group D: Weil pairing (see WeilPairing.lean) -/

-- The axiom `weil_pairing_primitive_root` (Group B, above) is discharged by
-- `weil_pairing_gives_primitive_root` in FLT/Assumptions/MazurProof/WeilPairing.lean.

/-! ## Group E: cyclic order bound, the hard Mazur core -/

/-- Mazur cyclic torsion: every rational torsion point has order in {1,...,10,12}. -/
axiom mazur_cyclic_order_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hord : HasRationalPointOfOrder E n) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)

/-- No elliptic curve over `ℚ` has a rational point of order at least `17`. -/
theorem no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n := by
  intro hord
  have hmem := mazur_cyclic_order_bound E hord
  simp [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

end MazurProof
