/-
Pure finite-abelian-group theory. NO elliptic geometry, NO new axioms.
Target: a finite abelian group that embeds into (ZMod N)² has at most two invariant
factors, i.e. ≅ ZMod m × ZMod n with m ∣ n. Needed by rational_torsion_two_invariant_factors.

GOAL: 0 sorry, and `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.Tactic

open scoped DirectSum

private noncomputable def zmodHom {A : Type*} [AddGroup A]
    (n : ℕ) (c : A) (hc : n • c = 0) : ZMod n →+ A :=
  ZMod.lift n ⟨zmultiplesHom A c, by
    simpa using (show (n : ℤ) • c = 0 by simpa using hc)⟩

@[simp]
private theorem zmodHom_intCast {A : Type*} [AddGroup A]
    (n : ℕ) (c : A) (hc : n • c = 0) (x : ℤ) :
    zmodHom n c hc (x : ZMod n) = x • c := by
  simp [zmodHom]

private noncomputable def zmodMulHom
    (n m : ℕ) (k : ℤ) (h : (m : ℤ) ∣ (n : ℤ) * k) : ZMod n →+ ZMod m :=
  zmodHom n (k : ZMod m) (by
    rw [nsmul_eq_mul]
    rw [← Int.cast_natCast n, ← Int.cast_mul]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) * k) m).2 h)

@[simp]
private theorem zmodMulHom_intCast
    (n m : ℕ) (k : ℤ) (h : (m : ℤ) ∣ (n : ℤ) * k) (x : ℤ) :
    zmodMulHom n m k h (x : ZMod n) = (x * k : ZMod m) := by
  simp [zmodMulHom, zsmul_eq_mul]

@[simp]
private theorem zmodMulHom_intCast_mul
    (n m : ℕ) (k : ℤ) (h : (m : ℤ) ∣ (n : ℤ) * k) (x c : ℤ) :
    zmodMulHom n m k h ((x : ZMod n) * (c : ZMod n)) =
      (x * c * k : ZMod m) := by
  rw [← Int.cast_mul, zmodMulHom_intCast]
  rw [Int.cast_mul]

private theorem lcm_eq_left_mul_div_gcd {a b : ℕ} (ha : a ≠ 0) :
    a.lcm b = a * (b / a.gcd b) := by
  by_cases hb : b = 0
  · simp [hb]
  · let g := a.gcd b
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc
      g * a.lcm b = a * b := Nat.gcd_mul_lcm a b
      _ = a * ((b / g) * g) := by
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
      _ = g * (a * (b / g)) := by ring

private theorem lcm_eq_right_mul_div_gcd {a b : ℕ} (hb : b ≠ 0) :
    a.lcm b = b * (a / a.gcd b) := by
  rw [Nat.lcm_comm, Nat.gcd_comm]
  exact lcm_eq_left_mul_div_gcd (a := b) (b := a) hb

private theorem gcd_mul_div_left {a b : ℕ} :
    a.gcd b * (a / a.gcd b) = a :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)

private theorem gcd_mul_div_right {a b : ℕ} :
    a.gcd b * (b / a.gcd b) = b :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)

private noncomputable def zmodProdGcdLcmForward
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ZMod a × ZMod b →+ ZMod (a.gcd b) × ZMod (a.lcm b) := by
  let g := a.gcd b
  let l := a.lcm b
  let α : ℕ := a / g
  let β : ℕ := b / g
  let A : ℤ := α
  let B : ℤ := β
  let r : ℤ := Nat.gcdA α β
  let s : ℤ := Nat.gcdB α β
  let hga : (g : ℤ) ∣ (a : ℤ) :=
    Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a b)
  let hgb : (g : ℤ) ∣ (b : ℤ) :=
    Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right a b)
  let hla : (l : ℤ) ∣ (a : ℤ) * (-B) := by
    have hnat : l ∣ a * β := by
      change a.lcm b ∣ a * (b / a.gcd b)
      rw [lcm_eq_left_mul_div_gcd (a := a) (b := b) ha]
    have hint : (l : ℤ) ∣ ((a * β : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 hnat
    rw [Int.natCast_mul] at hint
    simpa [B, mul_neg] using (dvd_neg.mpr hint)
  let hlb : (l : ℤ) ∣ (b : ℤ) * A := by
    have hnat : l ∣ b * α := by
      change a.lcm b ∣ b * (a / a.gcd b)
      rw [lcm_eq_right_mul_div_gcd (a := a) (b := b) hb]
    have hint : (l : ℤ) ∣ ((b * α : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 hnat
    simpa [A, Int.natCast_mul] using hint
  let f₁a := zmodMulHom a g r (dvd_mul_of_dvd_left hga r)
  let f₁b := zmodMulHom b g s (dvd_mul_of_dvd_left hgb s)
  let f₂a := zmodMulHom a l (-B) hla
  let f₂b := zmodMulHom b l A hlb
  exact (f₁a.coprod f₁b).prod (f₂a.coprod f₂b)

private noncomputable def zmodProdGcdLcmBackward (a b : ℕ) :
    ZMod (a.gcd b) × ZMod (a.lcm b) →+ ZMod a × ZMod b := by
  let g := a.gcd b
  let l := a.lcm b
  let α : ℕ := a / g
  let β : ℕ := b / g
  let A : ℤ := α
  let B : ℤ := β
  let r : ℤ := Nat.gcdA α β
  let s : ℤ := Nat.gcdB α β
  let hga : (a : ℤ) ∣ (g : ℤ) * A := by
    have hint : (a : ℤ) ∣ ((g * α : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (by rw [gcd_mul_div_left (a := a) (b := b)])
    simpa [A, Int.natCast_mul] using hint
  let hla : (a : ℤ) ∣ (l : ℤ) * (-s) := by
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (dvd_lcm_left a b)) (-s)
  let hgb : (b : ℤ) ∣ (g : ℤ) * B := by
    have hint : (b : ℤ) ∣ ((g * β : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (by rw [gcd_mul_div_right (a := a) (b := b)])
    simpa [B, Int.natCast_mul] using hint
  let hlb : (b : ℤ) ∣ (l : ℤ) * r := by
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (dvd_lcm_right a b)) r
  let f₁g := zmodMulHom g a A hga
  let f₁l := zmodMulHom l a (-s) hla
  let f₂g := zmodMulHom g b B hgb
  let f₂l := zmodMulHom l b r hlb
  exact (f₁g.coprod f₁l).prod (f₂g.coprod f₂l)

private noncomputable def zmodProdGcdLcmAddEquiv
    (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ZMod a × ZMod b ≃+ ZMod (a.gcd b) × ZMod (a.lcm b) := by
  let g := a.gcd b
  let l := a.lcm b
  let α : ℕ := a / g
  let β : ℕ := b / g
  let A : ℤ := α
  let B : ℤ := β
  let r : ℤ := Nat.gcdA α β
  let s : ℤ := Nat.gcdB α β
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
  have hcop : Nat.Coprime α β := Nat.coprime_div_gcd_div_gcd hgpos
  have hbez0 : ((α.gcd β : ℕ) : ℤ) = A * r + B * s := by
    simpa [A, B, r, s] using Nat.gcd_eq_gcd_ab α β
  have hbez : A * r + B * s = 1 := by
    simpa [hcop.gcd_eq_one] using hbez0.symm
  have hbez_comm : r * A + s * B = 1 := by
    linear_combination hbez
  refine
  { toFun := zmodProdGcdLcmForward a b ha hb
    invFun := zmodProdGcdLcmBackward a b
    left_inv := ?_
    right_inv := ?_
    map_add' := (zmodProdGcdLcmForward a b ha hb).map_add' }
  · rintro ⟨x, y⟩
    obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
    ext <;> simp [zmodProdGcdLcmForward, zmodProdGcdLcmBackward]
    · have hbezA : (r : ZMod a) * (A : ZMod a) + (s : ZMod a) * (B : ZMod a) = 1 := by
        calc
          (r : ZMod a) * (A : ZMod a) + (s : ZMod a) * (B : ZMod a)
              = ((r * A + s * B : ℤ) : ZMod a) := by
                rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
          _ = 1 := by rw [hbez_comm]; norm_num
      calc
        _ = (x : ZMod a) *
            ((r : ZMod a) * (A : ZMod a) + (s : ZMod a) * (B : ZMod a)) := by
              simp [A, B, α, β, r, s, g]
              rw [← Int.natCast_div a (a.gcd b), ← Int.natCast_div b (a.gcd b)]
              repeat rw [Int.cast_natCast]
              ring_nf
        _ = (x : ZMod a) := by rw [hbezA]; ring_nf
    · have hbezB : (A : ZMod b) * (r : ZMod b) + (B : ZMod b) * (s : ZMod b) = 1 := by
        calc
          (A : ZMod b) * (r : ZMod b) + (B : ZMod b) * (s : ZMod b)
              = ((A * r + B * s : ℤ) : ZMod b) := by
                rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
          _ = 1 := by rw [hbez]; norm_num
      calc
        _ = (y : ZMod b) *
            ((A : ZMod b) * (r : ZMod b) + (B : ZMod b) * (s : ZMod b)) := by
              simp [A, B, α, β, r, s, g]
              rw [← Int.natCast_div a (a.gcd b), ← Int.natCast_div b (a.gcd b)]
              repeat rw [Int.cast_natCast]
              ring_nf
        _ = (y : ZMod b) := by rw [hbezB]; ring_nf
  · rintro ⟨u, v⟩
    obtain ⟨u, rfl⟩ := ZMod.intCast_surjective u
    obtain ⟨v, rfl⟩ := ZMod.intCast_surjective v
    ext <;> simp [zmodProdGcdLcmForward, zmodProdGcdLcmBackward]
    · have hbezG : (A : ZMod g) * (r : ZMod g) + (B : ZMod g) * (s : ZMod g) = 1 := by
        calc
          (A : ZMod g) * (r : ZMod g) + (B : ZMod g) * (s : ZMod g)
              = ((A * r + B * s : ℤ) : ZMod g) := by
                rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
          _ = 1 := by rw [hbez]; norm_num
      calc
        _ = (u : ZMod g) *
            ((A : ZMod g) * (r : ZMod g) + (B : ZMod g) * (s : ZMod g)) := by
              simp [A, B, α, β, r, s, g]
              rw [← Int.natCast_div a (a.gcd b), ← Int.natCast_div b (a.gcd b)]
              repeat rw [Int.cast_natCast]
              ring_nf
        _ = (u : ZMod g) := by rw [hbezG]; ring_nf
    · have hbezL : (r : ZMod l) * (A : ZMod l) + (s : ZMod l) * (B : ZMod l) = 1 := by
        calc
          (r : ZMod l) * (A : ZMod l) + (s : ZMod l) * (B : ZMod l)
              = ((r * A + s * B : ℤ) : ZMod l) := by
                rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
          _ = 1 := by rw [hbez_comm]; norm_num
      calc
        _ = (v : ZMod l) *
            ((r : ZMod l) * (A : ZMod l) + (s : ZMod l) * (B : ZMod l)) := by
              simp [A, B, α, β, r, s, g]
              rw [← Int.natCast_div a (a.gcd b), ← Int.natCast_div b (a.gcd b)]
              repeat rw [Int.cast_natCast]
              ring_nf
        _ = (v : ZMod l) := by rw [hbezL]; ring_nf

private def finTwoDepAddEquiv
    (A : Fin 2 → Type*) [∀ i, AddCommGroup (A i)] :
    ((i : Fin 2) → A i) ≃+ A 0 × A 1 where
  toFun f := (f 0, f 1)
  invFun p := fun i =>
    Fin.cases p.1
      (fun j : Fin 1 => Fin.cases p.2 (fun k : Fin 0 => nomatch k) j)
      i
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    ext <;> rfl
  map_add' f g := by
    ext <;> rfl

/-- A finite abelian group embedding into `(ZMod N)²` decomposes as `ZMod m × ZMod n`
with `m ∣ n` and `Nat.card G = m * n`. -/
theorem finite_add_comm_group_embed_zmod_sq_invariantFactors_card
    {G : Type*} [AddCommGroup G] [Finite G]
    {N : ℕ} (hN : 0 < N)
    (ι : G →+ (ZMod N × ZMod N))
    (hι : Function.Injective ι) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m ∣ n ∧
      Nat.card G = m * n ∧
      Nonempty (G ≃+ ZMod m × ZMod n) := by
  classical
  let M := Fin 2 → ℤ
  let B := ZMod N × ZMod N
  let q : M →+ B :=
    { toFun := fun v => ((v 0 : ZMod N), (v 1 : ZMod N))
      map_zero' := by
        ext
        · change (((0 : ℤ) : ZMod N) = 0)
          simp
        · change (((0 : ℤ) : ZMod N) = 0)
          simp
      map_add' := by
        intro x y
        ext
        · change (((x 0 + y 0 : ℤ) : ZMod N) = (x 0 : ZMod N) + (y 0 : ZMod N))
          simp
        · change (((x 1 + y 1 : ℤ) : ZMod N) = (x 1 : ZMod N) + (y 1 : ZMod N))
          simp }
  let H : AddSubgroup B := ι.range
  haveI : Finite H := Finite.of_equiv G (AddMonoidHom.ofInjective hι)
  let K : Submodule ℤ M := H.toIntSubmodule.comap q.toIntLinearMap
  have hq_surj : Function.Surjective q := by
    rintro ⟨x, y⟩
    obtain ⟨x0, hx0⟩ := ZMod.intCast_surjective x
    obtain ⟨y0, hy0⟩ := ZMod.intCast_surjective y
    refine ⟨(fun i : Fin 2 => if i = 0 then x0 else y0), ?_⟩
    ext <;> simp [q, hx0, hy0]
  let qK : K →+ H :=
    { toFun := fun x =>
        ⟨q x.1, by
          have hx : q.toIntLinearMap x.1 ∈ H.toIntSubmodule := by
            change x.1 ∈ H.toIntSubmodule.comap q.toIntLinearMap
            exact x.2
          have hx' : q x.1 ∈ (H.toIntSubmodule : Set B) := hx
          rw [AddSubgroup.coe_toIntSubmodule] at hx'
          change q x.1 ∈ H
          exact hx'⟩
      map_zero' := by
        apply Subtype.ext
        change q (0 : K).1 = 0
        exact q.map_zero
      map_add' := by
        intro x y
        apply Subtype.ext
        change q (x + y : K).1 = q x.1 + q y.1
        exact q.map_add x.1 y.1 }
  have hqK_surj : Function.Surjective qK := by
    intro h
    obtain ⟨x, hx⟩ := hq_surj h.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change q x ∈ H
      rw [hx]
      exact h.2
    · apply Subtype.ext
      exact hx
  let L : Submodule ℤ K := qK.ker.toIntSubmodule
  let eKH : K ⧸ L ≃+ H := by
    change K ⧸ qK.ker ≃+ H
    exact QuotientAddGroup.quotientKerEquivOfSurjective qK hqK_surj
  haveI : Finite (K ⧸ L) := Finite.of_equiv H eKH.symm.toEquiv
  have hLrank : Module.finrank ℤ L = Module.finrank ℤ K :=
    (Submodule.finiteQuotient_iff L).mp inferInstance
  have hNzero : (N : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  let smulN : M →ₗ[ℤ] M := (LinearMap.lsmul ℤ M) (N : ℤ)
  let smulNK : M →ₗ[ℤ] K := smulN.codRestrict K (fun x => by
    have hq0 : q (smulN x) = 0 := by
      ext <;>
        simp [q, smulN, ZMod.intCast_zmod_eq_zero_iff_dvd] <;>
        exact dvd_mul_right _ _
    change q (smulN x) ∈ H
    rw [hq0]
    exact H.zero_mem)
  have hsmulNK_inj : Function.Injective smulNK := by
    intro x y hxy
    apply LinearMap.lsmul_injective (M := M) hNzero
    exact congr_arg Subtype.val hxy
  have hKrank : Module.finrank ℤ K = Module.finrank ℤ M := by
    apply le_antisymm
    · exact Submodule.finrank_le K
    · exact LinearMap.finrank_le_finrank_of_injective hsmulNK_inj
  let bM : Module.Basis (Fin 2) ℤ M := Pi.basisFun ℤ (Fin 2)
  let bK : Module.Basis (Fin 2) ℤ K :=
    Submodule.smithNormalFormBotBasis (N := K) bM hKrank
  let coeff : Fin 2 → ℕ :=
    fun i => (Submodule.smithNormalFormCoeffs bK hLrank i).natAbs
  have hcoeff_pos : ∀ i, 0 < coeff i := by
    intro i
    exact Int.natAbs_pos.2 (Submodule.smithNormalFormCoeffs_ne_zero bK hLrank i)
  let eSmith : K ⧸ L ≃+ ((i : Fin 2) → ZMod (coeff i)) :=
    Submodule.quotientEquivPiZMod L bK hLrank
  let ePair : K ⧸ L ≃+ ZMod (coeff 0) × ZMod (coeff 1) :=
    eSmith.trans (finTwoDepAddEquiv (fun i : Fin 2 => ZMod (coeff i)))
  let eGpair : G ≃+ ZMod (coeff 0) × ZMod (coeff 1) :=
    (AddMonoidHom.ofInjective hι).trans (eKH.symm.trans ePair)
  let m := (coeff 0).gcd (coeff 1)
  let n := (coeff 0).lcm (coeff 1)
  have hmpos : 0 < m := Nat.gcd_pos_of_pos_left _ (hcoeff_pos 0)
  have hnpos : 0 < n := Nat.lcm_pos (hcoeff_pos 0) (hcoeff_pos 1)
  have hmdvdn : m ∣ n :=
    dvd_trans (Nat.gcd_dvd_left (coeff 0) (coeff 1)) (Nat.dvd_lcm_left (coeff 0) (coeff 1))
  let eInv : ZMod (coeff 0) × ZMod (coeff 1) ≃+ ZMod m × ZMod n :=
    zmodProdGcdLcmAddEquiv (coeff 0) (coeff 1)
      (ne_of_gt (hcoeff_pos 0)) (ne_of_gt (hcoeff_pos 1))
  let eFinal : G ≃+ ZMod m × ZMod n := eGpair.trans eInv
  have hcard : Nat.card G = m * n := by
    rw [Nat.card_congr eFinal.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
  exact ⟨m, n, hmpos, hnpos, hmdvdn, hcard, ⟨eFinal⟩⟩
