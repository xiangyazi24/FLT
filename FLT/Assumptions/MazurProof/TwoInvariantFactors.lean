import Mathlib
import FLT.Assumptions.MazurProof.GroupTheory

/-! # Two Invariant Factor Decomposition for Finite Abelian Groups

## Statement

If a finite abelian group G satisfies:
- p-rank ≤ 1 for every odd prime p (no injective ZMod p × ZMod p →+ G), and
- 2-rank ≤ 2 (no injective ZMod 2 × ZMod 2 × ZMod 2 →+ G),

then G ≃ ZMod m × ZMod n for some positive m, n with m ∣ n.

## Proof outline

1. Primary decomposition G ≃ ⨁ᵢ ZMod(pᵢ^eᵢ) via Mathlib.
2. Set q(i) := pᵢ^eᵢ. Let T := {i | 2 ∣ q(i)}.
3. The rank conditions give: no odd prime divides two distinct q(i), and T.card ≤ 2.
4. If T.card ≤ 1: all q(i) pairwise coprime → CRT gives G ≃ ZMod(∏ q(i)).
   Take m = 1, n = ∏ q(i).
5. If T.card = 2: T = {a, b} with q(a), q(b) both 2-powers. WLOG q(a) ∣ q(b).
   Partition ι = {a} ∪ rest. The rest are pairwise coprime (no shared odd prime;
   only b is even among them, so no shared factor of 2).
   CRT collapses rest → ZMod N.
   Then G ≃ ZMod(q(a)) × ZMod N with q(a) ∣ N.

## Status

Self-contained public module. The identical proof exists privately in Axioms.lean
(lines 223-387); this file provides the public API.
-/

open scoped DirectSum Function

namespace MazurProof

/-! ## Structure and constructor -/

/-- Two invariant factor data for a finite abelian group:
    G ≃ ZMod m × ZMod n with m ∣ n, plus derived properties. -/
structure TwoInvariantFactorData' (G : Type*) [AddCommGroup G] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  equiv : Nonempty (G ≃+ ZMod m × ZMod n)
  order_n : ∃ x : G, addOrderOf x = n
  card_eq : Nat.card G = m * n

private lemma addOrderOf_prod_zero_one' {m n : ℕ} (hn : 0 < n) :
    addOrderOf ((0 : ZMod m), (1 : ZMod n)) = n := by
  rw [addOrderOf_eq_iff hn]
  constructor
  · ext <;> simp
  · intro k hk hkpos hzero
    have hz : (k : ZMod n) = 0 := by
      have h2 := congrArg Prod.snd hzero
      simpa using h2
    have hdvd_int : (n : ℤ) ∣ (k : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) n).mp (by simpa using hz)
    have hdvd : n ∣ k := by exact_mod_cast hdvd_int
    exact (Nat.not_le_of_gt hk) (Nat.le_of_dvd hkpos hdvd)

/-- Construct `TwoInvariantFactorData'` from an equivalence G ≃+ ZMod m × ZMod n. -/
noncomputable def twoInvariantFactorDataOfEquiv'
    (G : Type*) [AddCommGroup G] [Finite G] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (heq : Nonempty (G ≃+ ZMod m × ZMod n)) :
    TwoInvariantFactorData' G where
  m := m
  n := n
  m_pos := hm
  n_pos := hn
  dvd_mn := hmn
  equiv := heq
  order_n := by
    rcases heq with ⟨e⟩
    exact ⟨e.symm ((0 : ZMod m), (1 : ZMod n)), by
      rw [e.symm.addOrderOf_eq]; exact addOrderOf_prod_zero_one' hn⟩
  card_eq := by
    haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rcases heq with ⟨e⟩
    exact (Nat.card_congr e.toEquiv).trans (by simp)

/-! ## Helpers: Pi-type splitting and CRT partition -/

/-- Split a dependent function type by a finset into its in-set and out-of-set parts. -/
private noncomputable def piSplitAddEquiv' {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    ((i : ι) → A i) ≃+
      (((i : {i // i ∈ s}) → A i) × ((i : {i // i ∉ s}) → A i)) where
  toFun f := (fun i => f i, fun i => f i)
  invFun g i := if h : i ∈ s then g.1 ⟨i, h⟩ else g.2 ⟨i, h⟩
  left_inv f := by ext i; by_cases h : i ∈ s <;> simp [h]
  right_inv g := by ext i <;> simp [i.property]
  map_add' f g := by ext i <;> rfl

/-- Partition ⨁ᵢ ZMod(q(i)) into two CRT-collapsed halves:
    ZMod(∏ᵢ∈s q(i)) × ZMod(∏ᵢ∉s q(i)), given pairwise coprimality within each half. -/
private noncomputable def directSumPartitionEquiv' {ι : Type*} [Fintype ι]
    [DecidableEq ι] (q : ι → ℕ) (s : Finset ι)
    (hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ s} => q i))
    (hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ s} => q i)) :
    (⨁ i : ι, ZMod (q i)) ≃+
      ZMod (∏ i : {i // i ∈ s}, q i) × ZMod (∏ i : {i // i ∉ s}, q i) :=
  (DirectSum.addEquivProd (fun i : ι => ZMod (q i))).trans <|
    (piSplitAddEquiv' s (fun i : ι => ZMod (q i))).trans <|
      AddEquiv.prodCongr
        (ZMod.prodEquivPi (fun i : {i // i ∈ s} => q i) hcop₁).toAddEquiv.symm
        (ZMod.prodEquivPi (fun i : {i // i ∉ s} => q i) hcop₂).toAddEquiv.symm

/-! ## Injection lemmas

If a prime p divides components at distinct indices of a direct sum decomposition,
we can inject (ZMod p)^k into G. -/

/-- Two p-divisible components give an injection ZMod p × ZMod p →+ G. -/
private theorem square_injection_from_decomposition'
    {ι : Type*} [DecidableEq ι]
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j : ι) (hij : i ≠ j)
    (hpi : p ∣ n i) (hpj : p ∣ n j) :
    ∃ f : ZMod p × ZMod p →+ G, Function.Injective f := by
  obtain ⟨gi, hgi⟩ := zmod_contains_of_dvd p (n i) hp.pos (hn i) hpi
  obtain ⟨gj, hgj⟩ := zmod_contains_of_dvd p (n j) hp.pos (hn j) hpj
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

/-- Three p-divisible components give an injection ZMod p × ZMod p × ZMod p →+ G. -/
private theorem cube_injection_from_decomposition'
    {ι : Type*} [DecidableEq ι]
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hpi : p ∣ n i) (hpj : p ∣ n j) (hpk : p ∣ n k) :
    ∃ f : ZMod p × ZMod p × ZMod p →+ G, Function.Injective f := by
  obtain ⟨gi, hgi⟩ := zmod_contains_of_dvd p (n i) hp.pos (hn i) hpi
  obtain ⟨gj, hgj⟩ := zmod_contains_of_dvd p (n j) hp.pos (hn j) hpj
  obtain ⟨gk, hgk⟩ := zmod_contains_of_dvd p (n k) hp.pos (hn k) hpk
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

/-! ## Main theorem -/

/-- A finite abelian group with p-rank ≤ 1 (all odd p) and 2-rank ≤ 2
    has a two invariant factor decomposition G ≃ ZMod m × ZMod n with m ∣ n. -/
theorem finite_abelian_two_invariant_factors_exists'
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    ∃ d : TwoInvariantFactorData' G, True := by
  classical
  -- Step 1: Primary decomposition from Mathlib
  obtain ⟨ι, _hι, p, hp, exp, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  let q : ι → ℕ := fun i => p i ^ exp i
  have hqpos : ∀ i, 0 < q i := fun i => Nat.pow_pos (hp i).pos
  -- Step 2: No odd prime can divide two distinct components
  have hodd_rank : ∀ r : ℕ, Nat.Prime r → 2 < r → ∀ i j : ι,
      i ≠ j → r ∣ q i → r ∣ q j → False := by
    intro r hr hrgt i j hij hri hrj
    exact h_no_odd r hr hrgt
      (square_injection_from_decomposition' G q hqpos e r hr i j hij hri hrj)
  -- Step 3: At most 2 components divisible by 2
  let T : Finset ι := Finset.univ.filter (fun i => 2 ∣ q i)
  have hTle2 : T.card ≤ 2 := by
    by_contra hle
    have h2lt : 2 < T.card := by omega
    rcases Finset.two_lt_card.mp h2lt with ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩
    have h2i : 2 ∣ q i := by simpa [T] using hi
    have h2j : 2 ∣ q j := by simpa [T] using hj
    have h2k : 2 ∣ q k := by simpa [T] using hk
    exact h_no_two
      (cube_injection_from_decomposition' G q hqpos e 2 Nat.prime_two
        i j k hij hjk hik h2i h2j h2k)
  -- Step 4: Case split on T.card
  by_cases hTle1 : T.card ≤ 1
  · ---- Case T.card ≤ 1: all components pairwise coprime ----
    have hpair : Pairwise (Nat.Coprime on q) := by
      intro i j hij
      by_contra hcop
      rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with ⟨r, hr, hri, hrj⟩
      by_cases hr2 : r = 2
      · have hiT : i ∈ T := by simpa [T, hr2] using hri
        have hjT : j ∈ T := by simpa [T, hr2] using hrj
        have hone : 1 < T.card := Finset.one_lt_card.mpr ⟨i, hiT, j, hjT, hij⟩
        omega
      · have hrgt : 2 < r := by have h2le := hr.two_le; omega
        exact hodd_rank r hr hrgt i j hij hri hrj
    -- Partition s = ∅: m = ∏(∅) = 1, n = ∏(all)
    have hcop₁ : Pairwise (Nat.Coprime on fun i : {i // i ∈ (∅ : Finset ι)} => q i) := by
      intro i _ _
      cases i with | mk _ prop => simp at prop
    have hcop₂ : Pairwise (Nat.Coprime on fun i : {i // i ∉ (∅ : Finset ι)} => q i) := by
      intro i j hij
      exact hpair (fun hv => hij (Subtype.ext hv))
    let m := ∏ i : {i // i ∈ (∅ : Finset ι)}, q i
    let n := ∏ i : {i // i ∉ (∅ : Finset ι)}, q i
    have hmpos : 0 < m := by simp [m]
    have hnpos : 0 < n := by
      dsimp [n]
      exact Finset.prod_pos (fun i _ => hqpos i)
    have hmn : m ∣ n := by
      have hm : m = 1 := by simp [m]
      rw [hm]
      exact one_dvd n
    exact ⟨twoInvariantFactorDataOfEquiv' G hmpos hnpos hmn
      ⟨e.trans (directSumPartitionEquiv' q ∅ hcop₁ hcop₂)⟩, trivial⟩
  · ---- Case T.card = 2: two even (2-power) components ----
    have hT2 : T.card = 2 := by omega
    rcases Finset.card_eq_two.mp hT2 with ⟨a, b, hab, hT_eq⟩
    have haT : a ∈ T := by simp [hT_eq]
    have hbT : b ∈ T := by simp [hT_eq]
    have hqa_even : 2 ∣ q a := by simpa [T] using haT
    have hqb_even : 2 ∣ q b := by simpa [T] using hbT
    -- Both even components are powers of 2 (prime p dividing q(i)=p(i)^e(i) means p=p(i))
    have hpa : p a = 2 := by
      have h : 2 ∣ p a ^ exp a := by simpa [q] using hqa_even
      exact (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two (hp a) h).symm
    have hpb : p b = 2 := by
      have h : 2 ∣ p b ^ exp b := by simpa [q] using hqb_even
      exact (Nat.prime_eq_prime_of_dvd_pow Nat.prime_two (hp b) h).symm
    -- Both are 2-powers, so one divides the other
    have hcomp : q a ∣ q b ∨ q b ∣ q a := by
      rw [show q a = 2 ^ exp a by simp [q, hpa],
        show q b = 2 ^ exp b by simp [q, hpb]]
      rcases le_total (exp a) (exp b) with hle | hle
      · exact Or.inl (Nat.pow_dvd_pow 2 hle)
      · exact Or.inr (Nat.pow_dvd_pow 2 hle)
    -- Helper: complement of a singleton {a} where T = {a, b} is pairwise coprime.
    -- Any two elements outside {a} share no prime factor: an odd shared prime
    -- contradicts hodd_rank, and 2 would force both into T but T\{a} = {b}.
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
      · have hrgt : 2 < r := by have h2le := hr.two_le; omega
        exact hodd_rank r hr hrgt (i : ι) (j : ι) (fun hv => hij (Subtype.ext hv)) hri hrj
    -- A singleton set is vacuously pairwise coprime
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
    · -- Sub-case q(a) ∣ q(b): partition s = {a}, so m = q(a), n = ∏(rest)
      let s : Finset ι := {a}
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
      exact ⟨twoInvariantFactorDataOfEquiv' G hmpos hnpos hmn
        ⟨e.trans (directSumPartitionEquiv' q s hcop₁ hcop₂)⟩, trivial⟩
    · -- Sub-case q(b) ∣ q(a): partition s = {b}, so m = q(b), n = ∏(rest)
      let s : Finset ι := {b}
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
      exact ⟨twoInvariantFactorDataOfEquiv' G hmpos hnpos hmn
        ⟨e.trans (directSumPartitionEquiv' q s hcop₁ hcop₂)⟩, trivial⟩

end MazurProof
