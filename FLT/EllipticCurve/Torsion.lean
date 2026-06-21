/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine
open scoped DirectSum Function

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

private noncomputable def torsionByAddEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) :
    Submodule.torsionBy ℤ G (d : ℤ) ≃+ Submodule.torsionBy ℤ H (d : ℤ) where
  toFun x := ⟨e x, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul e (d : ℤ) (x : G)]
    simp [Submodule.smul_coe_torsionBy]⟩
  invFun y := ⟨e.symm y, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul e.symm (d : ℤ) (y : H)]
    simp [Submodule.smul_coe_torsionBy]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

private noncomputable def torsionByPiAddEquiv {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] (d : ℕ) :
    Submodule.torsionBy ℤ ((i : ι) → G i) (d : ℤ) ≃+
      ((i : ι) → Submodule.torsionBy ℤ (G i) (d : ℤ)) where
  toFun x i := ⟨(x : (i : ι) → G i) i, by
    rw [Submodule.mem_torsionBy_iff]
    have hx := Submodule.smul_coe_torsionBy (R := ℤ) (M := ((i : ι) → G i))
      (a := (d : ℤ)) x
    exact congrFun hx i⟩
  invFun y := ⟨fun i => (y i : G i), by
    rw [Submodule.mem_torsionBy_iff]
    ext i
    exact Submodule.smul_coe_torsionBy (R := ℤ) (M := G i) (a := (d : ℤ)) (y i)⟩
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl
  map_add' x y := by ext i; rfl

private noncomputable def torsionOfTorsionEquiv {A : Type*} [AddCommGroup A] {d n : ℕ}
    (hdn : d ∣ n) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A (n : ℤ)) (d : ℤ) ≃+
      Submodule.torsionBy ℤ A (d : ℤ) where
  toFun x := ⟨((x : Submodule.torsionBy ℤ A (n : ℤ)) : A), by
    rw [Submodule.mem_torsionBy_iff]
    have hx := Submodule.smul_coe_torsionBy (R := ℤ)
      (M := Submodule.torsionBy ℤ A (n : ℤ)) (a := (d : ℤ)) x
    exact congrArg Subtype.val hx⟩
  invFun y :=
    let hz : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdn
    ⟨⟨(y : A), Submodule.torsionBy_le_torsionBy_of_dvd (R := ℤ) (M := A)
      (d : ℤ) (n : ℤ) hz y.property⟩, by
      rw [Submodule.mem_torsionBy_iff]
      apply Subtype.ext
      exact Submodule.smul_coe_torsionBy (R := ℤ) (M := A) (a := (d : ℤ)) y⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl

private lemma zmod_prime_torsion_card {m p : ℕ} (hm0 : m ≠ 0) (hpm : p ∣ m) :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) (p : ℤ)) = p := by
  classical
  haveI : NeZero m := ⟨hm0⟩
  change Nat.card (AddSubgroup.torsionBy (ZMod m) (p : ℤ)) = p
  have hker : AddSubgroup.torsionBy (ZMod m) (p : ℤ) =
      (nsmulAddMonoidHom p : ZMod m →+ ZMod m).ker := by
    ext x
    simp [AddMonoidHom.mem_ker]
  calc
    Nat.card (AddSubgroup.torsionBy (ZMod m) (p : ℤ))
        = Nat.card ((nsmulAddMonoidHom p : ZMod m →+ ZMod m).ker) := by rw [hker]
    _ = (Nat.card (ZMod m)).gcd p := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) p
    _ = m.gcd p := by rw [Nat.card_zmod]
    _ = p := Nat.gcd_eq_right hpm

private lemma pi_zmod_prime_torsion_card {ι : Type*} [Fintype ι] {m : ι → ℕ} {p : ℕ}
    (hm0 : ∀ i, m i ≠ 0) (hpm : ∀ i, p ∣ m i) :
    Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ)) =
      p ^ Fintype.card ι := by
  classical
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  calc
    Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ))
        = Nat.card ((i : ι) → Submodule.torsionBy ℤ (ZMod (m i)) (p : ℤ)) :=
          Nat.card_congr (torsionByPiAddEquiv (G := fun i => ZMod (m i)) p).toEquiv
    _ = ∏ i, Nat.card (Submodule.torsionBy ℤ (ZMod (m i)) (p : ℤ)) := by
          rw [Nat.card_pi]
    _ = ∏ _i : ι, p := by
          apply Finset.prod_congr rfl
          intro i _hi
          exact zmod_prime_torsion_card (hm0 i) (hpm i)
    _ = p ^ Fintype.card ι := by simp

private lemma pi_zmod_card {ι : Type*} [Fintype ι] {m : ι → ℕ} (hm0 : ∀ i, m i ≠ 0) :
    Nat.card ((i : ι) → ZMod (m i)) = ∏ i, m i := by
  classical
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  rw [Nat.card_pi]
  simp

private noncomputable def piCommAddEquiv {ι κ : Type*} {G : ι → Type*}
    [∀ i, Add (G i)] :
    ((i : ι) → κ → G i) ≃+ (κ → (i : ι) → G i) where
  toFun x j i := x i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    ext j i
    rfl

private lemma prime_power_torsion_equiv {A : Type*} [AddCommGroup A] {p a r : ℕ}
    (hp : Nat.Prime p) (ha : 0 < a)
    (h1 : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ r)
    (hpa : Nat.card (Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) = (p ^ a) ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) ≃+
      (Fin r → ZMod (p ^ a))) := by
  classical
  let G := Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)
  have hpowa_pos : 0 < p ^ a := pow_pos hp.pos a
  haveI : Finite G := Nat.finite_of_card_ne_zero (by
    change Nat.card (Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) ≠ 0
    rw [hpa]
    exact (pow_pos hpowa_pos r).ne')
  obtain ⟨ι, hι, m, hmgt, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  letI : Fintype ι := hι
  have hm0 : ∀ i, m i ≠ 0 := fun i => ne_of_gt ((zero_lt_one).trans (hmgt i))
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  let H := ⨁ i : ι, ZMod (m i)
  have hkillH_nat : ∀ y : H, (p ^ a) • y = 0 := by
    intro y
    have hx := Submodule.smul_torsionBy (R := ℤ) (M := A)
      (a := ((p ^ a : ℕ) : ℤ)) (e.symm y)
    have hy_int : (((p ^ a : ℕ) : ℤ) • y = 0) := by
      calc
        ((p ^ a : ℕ) : ℤ) • y = e (((p ^ a : ℕ) : ℤ) • e.symm y) := by
          rw [map_zsmul, e.apply_symm_apply]
        _ = 0 := by rw [hx, map_zero]
    rw [← natCast_zsmul y (p ^ a)]
    exact hy_int
  have hmdiv : ∀ i, m i ∣ p ^ a := by
    intro i
    have hof : (DirectSum.of (fun i : ι => ZMod (m i)) i) ((p ^ a) •
        (1 : ZMod (m i))) = 0 := by
      rw [map_nsmul]
      exact hkillH_nat (DirectSum.of (fun i : ι => ZMod (m i)) i (1 : ZMod (m i)))
    have hcoord : (p ^ a) • (1 : ZMod (m i)) = 0 := by
      have h := congrArg (fun z : H => z i) hof
      simpa [H, DirectSum.of_eq_same] using h
    simpa [ZMod.addOrderOf_one] using
      (addOrderOf_dvd_iff_nsmul_eq_zero (x := (1 : ZMod (m i))) (n := p ^ a)).mpr hcoord
  have hp_dvd_m : ∀ i, p ∣ m i := by
    intro i
    obtain ⟨k, _hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).1 (hmdiv i)
    rw [hk_eq]
    apply dvd_pow_self
    intro hk0
    have hmi1 : m i = 1 := by simpa [hk0] using hk_eq
    exact (ne_of_gt (hmgt i)) hmi1
  have hcard_torsion_H :
      Nat.card (Submodule.torsionBy ℤ H (p : ℤ)) = p ^ Fintype.card ι := by
    calc
      Nat.card (Submodule.torsionBy ℤ H (p : ℤ))
          = Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ)) :=
            Nat.card_congr (torsionByAddEquiv
              (DirectSum.addEquivProd (fun i : ι => ZMod (m i))) p).toEquiv
      _ = p ^ Fintype.card ι := pi_zmod_prime_torsion_card hm0 hp_dvd_m
  have hcardι : Fintype.card ι = r := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ Fintype.card ι = Nat.card (Submodule.torsionBy ℤ H (p : ℤ)) :=
        hcard_torsion_H.symm
      _ = Nat.card (Submodule.torsionBy ℤ G (p : ℤ)) :=
          (Nat.card_congr (torsionByAddEquiv e p).toEquiv).symm
      _ = Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) :=
          Nat.card_congr (torsionOfTorsionEquiv (A := A) (d := p) (n := p ^ a)
            (dvd_pow_self p ha.ne')).toEquiv
      _ = p ^ r := h1
  have hprod : ∏ i, m i = (p ^ a) ^ r := by
    calc
      ∏ i, m i = Nat.card ((i : ι) → ZMod (m i)) := (pi_zmod_card hm0).symm
      _ = Nat.card H :=
          (Nat.card_congr (DirectSum.addEquivProd (fun i : ι => ZMod (m i))).toEquiv).symm
      _ = Nat.card G := (Nat.card_congr e.toEquiv).symm
      _ = (p ^ a) ^ r := hpa
  have hprod_const : (∏ i, m i) = ∏ _i : ι, p ^ a := by
    rw [hprod, Finset.prod_const, Finset.card_univ, hcardι]
  have hm_eq : ∀ i, m i = p ^ a := by
    intro i
    apply le_antisymm
    · exact Nat.le_of_dvd hpowa_pos (hmdiv i)
    · by_contra hnot
      have hlt : m i < p ^ a := lt_of_not_ge hnot
      have hprod_lt : (∏ j, m j) < ∏ _j : ι, p ^ a := by
        exact Finset.prod_lt_prod (s := Finset.univ)
          (fun j _ => (zero_lt_one).trans (hmgt j))
          (fun j _ => Nat.le_of_dvd hpowa_pos (hmdiv j))
          ⟨i, Finset.mem_univ i, hlt⟩
      rw [hprod_const] at hprod_lt
      exact (lt_irrefl _) hprod_lt
  let e_m : ((i : ι) → ZMod (m i)) ≃+ ((i : ι) → ZMod (p ^ a)) :=
    AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (hm_eq i)).toAddEquiv
  let e_idx : ((i : ι) → ZMod (p ^ a)) ≃+ (Fin r → ZMod (p ^ a)) :=
    { Equiv.piCongrLeft (fun _ : Fin r => ZMod (p ^ a)) (Fintype.equivFinOfCardEq hcardι) with
      map_add' := by
        intro x y
        ext j
        simp [Equiv.piCongrLeft] }
  exact ⟨e.trans <| (DirectSum.addEquivProd (fun i : ι => ZMod (m i))).trans <|
    e_m.trans e_idx⟩

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  by_cases hn1 : n = 1
  · subst n
    haveI : Unique (Submodule.torsionBy ℤ A (1 : ℤ)) := {
      default := 0
      uniq := by
        intro x
        ext
        have hx0 : (x : A) ∈ (⊥ : Submodule ℤ A) := by
          simpa [Submodule.torsionBy_one] using x.property
        simpa using hx0 }
    haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
    exact ⟨AddEquiv.ofUnique⟩
  let ι := {p : ℕ // p ∈ n.primeFactors}
  let q : ι → ℕ := fun p => p.1 ^ n.factorization p.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hp : ∀ p : ι, Nat.Prime p.1 := fun p => Nat.prime_of_mem_primeFactors p.2
  have hpdvd : ∀ p : ι, p.1 ∣ n := fun p => (Nat.mem_primeFactors.mp p.2).2.1
  have hfac_pos : ∀ p : ι, 0 < n.factorization p.1 := fun p =>
    (hp p).factorization_pos_of_dvd hn0 (hpdvd p)
  have hq_dvd : ∀ p : ι, q p ∣ n := by
    intro p
    exact ((hp p).pow_dvd_iff_le_factorization hn0).mpr le_rfl
  have hcomponent :
      ∀ p : ι, Nonempty (Submodule.torsionBy ℤ A (q p : ℤ) ≃+
        (Fin r → ZMod (q p))) := by
    intro p
    apply prime_power_torsion_equiv (hp p) (hfac_pos p)
    · simpa using h p.1 (hpdvd p)
    · simpa [q] using h (q p) (hq_dvd p)
  let G := Submodule.torsionBy ℤ A (n : ℤ)
  have hprod_nat : ∏ p : ι, q p = n := by
    simpa [ι, q] using (Nat.prod_pow_primeFactors_factorization hn0).symm
  have hprod_int : ∏ p : ι, (q p : ℤ) = (n : ℤ) := by
    exact_mod_cast hprod_nat
  have hcop :
      ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime fun p : ι => (q p : ℤ)) := by
    intro p _hpmem q' _hqmem hpq
    have hpq_ne : p.1 ≠ q'.1 := by
      intro hval
      exact hpq (Subtype.ext hval)
    exact (Nat.coprime_pow_primes (n.factorization p.1) (n.factorization q'.1)
      (hp p) (hp q') hpq_ne).isCoprime
  have htorsion :
      Module.IsTorsionBy ℤ G (∏ p ∈ (Finset.univ : Finset ι), (q p : ℤ)) := by
    intro x
    have hprod_int' : (∏ p ∈ (Finset.univ : Finset ι), (q p : ℤ)) = (n : ℤ) := by
      simpa using hprod_int
    rw [hprod_int']
    apply Subtype.ext
    exact Submodule.smul_coe_torsionBy (R := ℤ) (M := A) (a := (n : ℤ)) x
  have hinternal := Submodule.torsionBy_isInternal (R := ℤ) (M := G)
    (S := (Finset.univ : Finset ι)) (q := fun p : ι => (q p : ℤ)) hcop htorsion
  let σ := (Finset.univ : Finset ι)
  let decomp : G ≃+ ⨁ p : σ, Submodule.torsionBy ℤ G (q p.1 : ℤ) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap
      (fun p : σ => Submodule.torsionBy ℤ G (q p.1 : ℤ))) hinternal).symm.toAddEquiv
  let compEquiv : (p : σ) →
      Submodule.torsionBy ℤ G (q p.1 : ℤ) ≃+ (Fin r → ZMod (q p.1)) :=
    fun p => (torsionOfTorsionEquiv (A := A) (d := q p.1) (n := n) (hq_dvd p.1)).trans
      (hcomponent p.1).some
  let comps : (⨁ p : σ, Submodule.torsionBy ℤ G (q p.1 : ℤ)) ≃+
      ⨁ p : σ, (Fin r → ZMod (q p.1)) :=
    DFinsupp.mapRange.addEquiv compEquiv
  let prodEquiv : (⨁ p : σ, (Fin r → ZMod (q p.1))) ≃+
      ((p : σ) → Fin r → ZMod (q p.1)) :=
    DirectSum.addEquivProd (fun p : σ => Fin r → ZMod (q p.1))
  let univEquiv : σ ≃ ι := Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)
  let reindex : ((p : σ) → Fin r → ZMod (q p.1)) ≃+
      ((p : ι) → Fin r → ZMod (q p)) :=
    { toFun := fun x p => x (univEquiv.symm p)
      invFun := fun x p => x (univEquiv p)
      left_inv := by
        intro x
        ext p j
        rfl
      right_inv := by
        intro x
        ext p j
        rfl
      map_add' := by
        intro x y
        ext p j
        rfl }
  let swap : ((p : ι) → Fin r → ZMod (q p)) ≃+
      (Fin r → (p : ι) → ZMod (q p)) :=
    piCommAddEquiv
  let crt : (Fin r → (p : ι) → ZMod (q p)) ≃+ (Fin r → ZMod n) :=
    AddEquiv.piCongrRight fun _ =>
      (ZMod.equivPi n hn0).symm.toAddEquiv
  exact ⟨decomp.trans <| comps.trans <| prodEquiv.trans <| reindex.trans <| swap.trans crt⟩

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul P := by
        change Points.map E ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) P = P
        rw [show ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K from rfl]
        simp [Points.map_id]
      mul_smul g h P := by
        change Points.map E ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P =
          Points.map E (g : K →ₐ[k] K) (Points.map E (h : K →ₐ[k] K) P)
        rw [show ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) =
          (g : K →ₐ[k] K).comp h from rfl]
        have hcomp := Points.map_comp E K K K (h : K →ₐ[k] K) (g : K →ₐ[k] K)
        rw [← AddMonoidHom.comp_apply]
        congr 1
        exact hcomp.symm
      smul_zero g := by
        change Points.map E (g : K →ₐ[k] K) 0 = 0
        exact map_zero _
      smul_add g P Q := by
        change Points.map E (g : K →ₐ[k] K) (P + Q) =
          Points.map E (g : K →ₐ[k] K) P + Points.map E (g : K →ₐ[k] K) Q
        exact map_add _ P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
