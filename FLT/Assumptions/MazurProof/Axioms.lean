import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.TorsionFinite

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

private structure TwoInvariantFactorData (G : Type*) [AddCommGroup G] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  equiv : Nonempty (G ≃+ ZMod m × ZMod n)
  order_n : ∃ x : G, addOrderOf x = n
  card_eq : Nat.card G = m * n

private lemma addOrderOf_prod_zero_one {m n : ℕ} (hn : 0 < n) :
    addOrderOf ((0 : ZMod m), (1 : ZMod n)) = n := by
  rw [addOrderOf_eq_iff hn]
  constructor
  · ext <;> simp
  · intro k hk hkpos hzero
    have hz : (k : ZMod n) = 0 := by
      have h2 := congrArg Prod.snd hzero
      simpa using h2
    have hdvd_int : (n : ℤ) ∣ (k : ℤ) := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) n).mp (by simpa using hz)
    have hdvd : n ∣ k := by exact_mod_cast hdvd_int
    exact (Nat.not_le_of_gt hk) (Nat.le_of_dvd hkpos hdvd)

private noncomputable def twoInvariantFactorDataOfEquiv
    (G : Type*) [AddCommGroup G] [Finite G] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (heq : Nonempty (G ≃+ ZMod m × ZMod n)) :
    TwoInvariantFactorData G where
  m := m
  n := n
  m_pos := hm
  n_pos := hn
  dvd_mn := hmn
  equiv := heq
  order_n := by
    rcases heq with ⟨e⟩
    refine ⟨e.symm ((0 : ZMod m), (1 : ZMod n)), ?_⟩
    rw [e.symm.addOrderOf_eq]
    exact addOrderOf_prod_zero_one hn
  card_eq := by
    haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rcases heq with ⟨e⟩
    calc
      Nat.card G = Nat.card (ZMod m × ZMod n) := Nat.card_congr e.toEquiv
      _ = m * n := by simp

private noncomputable def piSplitAddEquiv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    ((i : ι) → A i) ≃+
      (((i : {i // i ∈ s}) → A i) × ((i : {i // i ∉ s}) → A i)) where
  toFun f := (fun i => f i, fun i => f i)
  invFun g := fun i => if h : i ∈ s then g.1 ⟨i, h⟩ else g.2 ⟨i, h⟩
  left_inv f := by
    ext i
    by_cases h : i ∈ s <;> simp [h]
  right_inv g := by
    ext i <;> simp [i.property]
  map_add' f g := by
    ext i <;> rfl

private noncomputable def directSumZModPartitionAddEquiv {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ι → ℕ) (s : Finset ι)
    (hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ s} => q i))
    (hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ s} => q i)) :
    (⨁ i : ι, ZMod (q i)) ≃+
      ZMod (∏ i : {i // i ∈ s}, q i) × ZMod (∏ i : {i // i ∉ s}, q i) :=
  (DirectSum.addEquivProd (fun i : ι => ZMod (q i))).trans <|
    (piSplitAddEquiv s (fun i : ι => ZMod (q i))).trans <|
      AddEquiv.prodCongr
        (ZMod.prodEquivPi (fun i : {i // i ∈ s} => q i) hcop₁).toAddEquiv.symm
        (ZMod.prodEquivPi (fun i : {i // i ∉ s} => q i) hcop₂).toAddEquiv.symm

private theorem square_injection_of_two_divisible'
    {ι : Type*} [DecidableEq ι]
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hnpos : ∀ i, 0 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j : ι) (hij : i ≠ j)
    (hpi : p ∣ n i) (hpj : p ∣ n j) :
    ∃ f : ZMod p × ZMod p →+ G, Function.Injective f := by
  obtain ⟨gi, hgi⟩ := MazurProof.zmod_contains_of_dvd p (n i) hp.pos (hnpos i) hpi
  obtain ⟨gj, hgj⟩ := MazurProof.zmod_contains_of_dvd p (n j) hp.pos (hnpos j) hpj
  let fi := (DirectSum.of (fun k => ZMod (n k)) i).comp gi
  let fj := (DirectSum.of (fun k => ZMod (n k)) j).comp gj
  let f : ZMod p × ZMod p →+ ⨁ k : ι, ZMod (n k) :=
    { toFun := fun xy => fi xy.1 + fj xy.2
      map_zero' := by simp [fi, fj]
      map_add' := by intro x y; simp [fi, fj, Prod.fst_add, Prod.snd_add]; abel }
  have hf_inj : Function.Injective f := by
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    have h_eq : fi x₁ + fj x₂ = fi y₁ + fj y₂ := hxy
    have hi_eq : (fi x₁ + fj x₂) i = (fi y₁ + fj y₂) i := by rw [h_eq]
    have hj_eq : (fi x₁ + fj x₂) j = (fi y₁ + fj y₂) j := by rw [h_eq]
    simp only [fi, fj, AddMonoidHom.comp_apply, DirectSum.add_apply] at hi_eq hj_eq
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij, add_zero,
        DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij, add_zero] at hi_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same, zero_add] at hj_eq
    exact Prod.ext (hgi hi_eq) (hgj hj_eq)
  exact ⟨e.symm.toAddMonoidHom.comp f, e.symm.injective.comp hf_inj⟩

private theorem cube_injection_of_three_divisible'
    {ι : Type*} [DecidableEq ι]
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hnpos : ∀ i, 0 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hpi : p ∣ n i) (hpj : p ∣ n j) (hpk : p ∣ n k) :
    ∃ f : ZMod p × ZMod p × ZMod p →+ G, Function.Injective f := by
  obtain ⟨gi, hgi⟩ := MazurProof.zmod_contains_of_dvd p (n i) hp.pos (hnpos i) hpi
  obtain ⟨gj, hgj⟩ := MazurProof.zmod_contains_of_dvd p (n j) hp.pos (hnpos j) hpj
  obtain ⟨gk, hgk⟩ := MazurProof.zmod_contains_of_dvd p (n k) hp.pos (hnpos k) hpk
  let fi := (DirectSum.of (fun l => ZMod (n l)) i).comp gi
  let fj := (DirectSum.of (fun l => ZMod (n l)) j).comp gj
  let fk := (DirectSum.of (fun l => ZMod (n l)) k).comp gk
  let f : ZMod p × ZMod p × ZMod p →+ ⨁ l : ι, ZMod (n l) :=
    { toFun := fun xyz => fi xyz.1 + fj xyz.2.1 + fk xyz.2.2
      map_zero' := by simp [fi, fj, fk]
      map_add' := by intro x y; simp [fi, fj, fk, Prod.fst_add, Prod.snd_add]; abel }
  have hf_inj : Function.Injective f := by
    intro ⟨x₁, x₂, x₃⟩ ⟨y₁, y₂, y₃⟩ hxy
    have h_eq : fi x₁ + fj x₂ + fk x₃ = fi y₁ + fj y₂ + fk y₃ := hxy
    have hi_eq : (fi x₁ + fj x₂ + fk x₃) i = (fi y₁ + fj y₂ + fk y₃) i := by rw [h_eq]
    have hj_eq : (fi x₁ + fj x₂ + fk x₃) j = (fi y₁ + fj y₂ + fk y₃) j := by rw [h_eq]
    have hk_eq : (fi x₁ + fj x₂ + fk x₃) k = (fi y₁ + fj y₂ + fk y₃) k := by rw [h_eq]
    simp only [fi, fj, fk, AddMonoidHom.comp_apply, DirectSum.add_apply] at hi_eq hj_eq hk_eq
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij,
        DirectSum.of_eq_of_ne _ _ _ hik, add_zero, add_zero,
        DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij,
        DirectSum.of_eq_of_ne _ _ _ hik, add_zero, add_zero] at hi_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same,
        DirectSum.of_eq_of_ne _ _ _ hjk, zero_add, add_zero,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same,
        DirectSum.of_eq_of_ne _ _ _ hjk, zero_add, add_zero] at hj_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hik),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_same,
        zero_add, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hik),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_same,
        zero_add, zero_add] at hk_eq
    exact Prod.ext (hgi hi_eq) (Prod.ext (hgj hj_eq) (hgk hk_eq))
  exact ⟨e.symm.toAddMonoidHom.comp f, e.symm.injective.comp hf_inj⟩

private theorem finite_addCommGroup_two_invariant_factors_exists
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    ∃ d : TwoInvariantFactorData G, True := by
  classical
  obtain ⟨ι, _hι, p, hp, exp, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  let q : ι → ℕ := fun i => p i ^ exp i
  have hqpos : ∀ i, 0 < q i := by
    intro i
    exact Nat.pow_pos (hp i).pos
  let T : Finset ι := Finset.univ.filter (fun i => 2 ∣ q i)
  have hodd_rank : ∀ r : ℕ, Nat.Prime r → 2 < r → ∀ i j : ι,
      i ≠ j → r ∣ q i → r ∣ q j → False := by
    intro r hr hrgt i j hij hri hrj
    exact h_no_odd r hr hrgt
      (square_injection_of_two_divisible' G q hqpos e r hr i j hij hri hrj)
  have hTle2 : T.card ≤ 2 := by
    by_contra hle
    have h2lt : 2 < T.card := by omega
    rcases Finset.two_lt_card.mp h2lt with ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩
    have h2i : 2 ∣ q i := by simpa [T] using hi
    have h2j : 2 ∣ q j := by simpa [T] using hj
    have h2k : 2 ∣ q k := by simpa [T] using hk
    exact h_no_two
      (cube_injection_of_three_divisible' G q hqpos e 2 Nat.prime_two i j k hij hjk hik h2i h2j h2k)
  by_cases hTle1 : T.card ≤ 1
  · have hpair : Pairwise (Nat.Coprime on q) := by
      intro i j hij
      by_contra hcop
      rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨r, hr, hri, hrj⟩
      by_cases hr2 : r = 2
      · have hiT : i ∈ T := by simpa [T, hr2] using hri
        have hjT : j ∈ T := by simpa [T, hr2] using hrj
        have hone : 1 < T.card := Finset.one_lt_card.mpr ⟨i, hiT, j, hjT, hij⟩
        omega
      · have hrgt : 2 < r := by
          have h2le := hr.two_le
          omega
        exact hodd_rank r hr hrgt i j hij hri hrj
    have hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ (∅ : Finset ι)} => q i) := by
      intro i _j _hij
      cases i with
      | mk _ prop => simp at prop
    have hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ (∅ : Finset ι)} => q i) := by
      intro i j hij
      exact hpair (fun hv => hij (Subtype.ext hv))
    let m := ∏ i : {i // i ∈ (∅ : Finset ι)}, q i
    let n := ∏ i : {i // i ∉ (∅ : Finset ι)}, q i
    have hmpos : 0 < m := by
      simp [m]
    have hnpos : 0 < n := by
      dsimp [n]
      exact Finset.prod_pos (fun i _ => hqpos i)
    have hmn : m ∣ n := by
      have hm : m = 1 := by simp [m]
      rw [hm]
      exact one_dvd n
    exact ⟨twoInvariantFactorDataOfEquiv G hmpos hnpos hmn
      ⟨e.trans (directSumZModPartitionAddEquiv q ∅ hcop₁ hcop₂)⟩, trivial⟩
  · have hT2 : T.card = 2 := by omega
    rcases Finset.card_eq_two.mp hT2 with ⟨a, b, hab, hT_eq⟩
    have haT : a ∈ T := by simpa [hT_eq]
    have hbT : b ∈ T := by simpa [hT_eq]
    have hqa_even : 2 ∣ q a := by simpa [T] using haT
    have hqb_even : 2 ∣ q b := by simpa [T] using hbT
    have hpa : p a = 2 := by
      have h : 2 ∣ p a ^ exp a := by simpa [q] using hqa_even
      exact (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two (hp a) h).symm
    have hpb : p b = 2 := by
      have h : 2 ∣ p b ^ exp b := by simpa [q] using hqb_even
      exact (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two (hp b) h).symm
    have hcomp : q a ∣ q b ∨ q b ∣ q a := by
      rw [show q a = 2 ^ exp a by simp [q, hpa],
        show q b = 2 ^ exp b by simp [q, hpb]]
      rcases le_total (exp a) (exp b) with hle | hle
      · exact Or.inl (Nat.pow_dvd_pow 2 hle)
      · exact Or.inr (Nat.pow_dvd_pow 2 hle)
    have hpair_compl : ∀ {a b : ι}, a ≠ b → T = {a, b} →
        Pairwise (Nat.Coprime on fun i : {i // i ∉ ({a} : Finset ι)} => q i) := by
      intro a b hab hTab i j hij
      by_contra hcop
      rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨r, hr, hri, hrj⟩
      by_cases hr2 : r = 2
      · have hiT : (i : ι) ∈ T := by simpa [T, hr2] using hri
        have hjT : (j : ι) ∈ T := by simpa [T, hr2] using hrj
        have hi_pair : (i : ι) ∈ ({a, b} : Finset ι) := by simpa [hTab] using hiT
        have hj_pair : (j : ι) ∈ ({a, b} : Finset ι) := by simpa [hTab] using hjT
        have hi_cases : (i : ι) = a ∨ (i : ι) = b := by simpa using hi_pair
        have hj_cases : (j : ι) = a ∨ (j : ι) = b := by simpa using hj_pair
        have hi_ne_a : (i : ι) ≠ a := by
          intro hia
          exact i.property (Finset.mem_singleton.mpr hia)
        have hj_ne_a : (j : ι) ≠ a := by
          intro hja
          exact j.property (Finset.mem_singleton.mpr hja)
        have hi_eq_b : (i : ι) = b := hi_cases.resolve_left hi_ne_a
        have hj_eq_b : (j : ι) = b := hj_cases.resolve_left hj_ne_a
        exact hij (Subtype.ext (hi_eq_b.trans hj_eq_b.symm))
      · have hrgt : 2 < r := by
          have h2le := hr.two_le
          omega
        exact hodd_rank r hr hrgt (i : ι) (j : ι) (fun hv => hij (Subtype.ext hv)) hri hrj
    have hpair_singleton : ∀ {a : ι},
        Pairwise (Nat.Coprime on fun i : {i // i ∈ ({a} : Finset ι)} => q i) := by
      intro a i j hij
      exfalso
      apply hij
      ext
      have hi : (i : ι) = a := Finset.mem_singleton.mp i.property
      have hj : (j : ι) = a := Finset.mem_singleton.mp j.property
      exact hi.trans hj.symm
    rcases hcomp with hqab | hqba
    · let s : Finset ι := {a}
      have hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ s} => q i) := by
        simpa [s] using (hpair_singleton (a := a))
      have hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ s} => q i) := by
        simpa [s] using (hpair_compl (a := a) (b := b) hab hT_eq)
      let m := ∏ i : {i // i ∈ s}, q i
      let n := ∏ i : {i // i ∉ s}, q i
      have hmpos : 0 < m := by
        dsimp [m]
        exact Finset.prod_pos (fun i _ => hqpos i)
      have hnpos : 0 < n := by
        dsimp [n]
        exact Finset.prod_pos (fun i _ => hqpos i)
      have hmn : m ∣ n := by
        have hm_eq : m = q a := by simp [m, s]
        have hb_not : b ∉ s := by simp [s, hab.symm]
        have hqbdvd : q b ∣ n := by
          dsimp [n]
          exact Finset.dvd_prod_of_mem
            (s := (Finset.univ : Finset {i // i ∉ s}))
            (f := fun i : {i // i ∉ s} => q i) (Finset.mem_univ ⟨b, hb_not⟩)
        rw [hm_eq]
        exact hqab.trans hqbdvd
      exact ⟨twoInvariantFactorDataOfEquiv G hmpos hnpos hmn
        ⟨e.trans (directSumZModPartitionAddEquiv q s hcop₁ hcop₂)⟩, trivial⟩
    · let s : Finset ι := {b}
      have hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ s} => q i) := by
        simpa [s] using (hpair_singleton (a := b))
      have hT_eq' : T = {b, a} := by simpa [Finset.pair_comm] using hT_eq
      have hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ s} => q i) := by
        simpa [s] using (hpair_compl (a := b) (b := a) hab.symm hT_eq')
      let m := ∏ i : {i // i ∈ s}, q i
      let n := ∏ i : {i // i ∉ s}, q i
      have hmpos : 0 < m := by
        dsimp [m]
        exact Finset.prod_pos (fun i _ => hqpos i)
      have hnpos : 0 < n := by
        dsimp [n]
        exact Finset.prod_pos (fun i _ => hqpos i)
      have hmn : m ∣ n := by
        have hm_eq : m = q b := by simp [m, s]
        have ha_not : a ∉ s := by simp [s, hab]
        have hqadvd : q a ∣ n := by
          dsimp [n]
          exact Finset.dvd_prod_of_mem
            (s := (Finset.univ : Finset {i // i ∉ s}))
            (f := fun i : {i // i ∉ s} => q i) (Finset.mem_univ ⟨a, ha_not⟩)
        rw [hm_eq]
        exact hqba.trans hqadvd
      exact ⟨twoInvariantFactorDataOfEquiv G hmpos hnpos hmn
        ⟨e.trans (directSumZModPartitionAddEquiv q s hcop₁ hcop₂)⟩, trivial⟩

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
  let d : TwoInvariantFactorData G :=
    Classical.choose
      (finite_addCommGroup_two_invariant_factors_exists G
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

/-- No elliptic curve over `ℚ` has a rational point of order at least `17`. -/
axiom no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n

end MazurProof
