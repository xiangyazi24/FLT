import Mathlib

/-!
# N18 Block 5 — 3-adic formal-kernel annihilator ([21]) via a minimal interface

Fable-designed retarget of the order-18 rank-0 core's Block 5. The supersingular height-2
`[3]`-series Newton polygon is retired; the content is three height-agnostic lemmas over an
abstract formal kernel `FormalKernel18` (Ê₀(𝔪) of E₀=162.c3 at π|3 in L=ℚ(ζ₉)⁺):
- (A) no prime-to-3 torsion — from valuation-domination of unit multiplication;
- (B) 𝔪²-torsion-free — the ONE deep analytic input, CARRIED as the field `torsion_val_eq_one`;
- (C) 3-power torsion has exponent 3 — the corrected valuation step (lower bound only).
Assembly: [21] annihilates E₀(L)_tors via per-element Bézout primary decomposition (no global
finiteness). B is discharged later (formal-log iso on 𝔪², Silverman AEC IV.6.4(b)).
-/

open scoped Classical
open PowerSeries

/-- Formal kernel Ê₀(𝔪) of E₀=162.c3 at π|3 in L=ℚ(ζ₉)⁺.
    Normalization v(π)=1 ⇒ v(3)=3, e=3, residue char p=3. -/
structure FormalKernel18 where
  M : Type*
  addCommGroup : AddCommGroup M
  /-- valuation of the formal parameter z = -x/y; ⊤ ↔ z = 0. -/
  val : M → ℕ∞
  val_eq_top : ∀ z : M, val z = ⊤ ↔ z = 0
  /-- every point lies in 𝔪: v(z) ≥ 1. -/
  one_le_val : ∀ z : M, z ≠ 0 → 1 ≤ val z
  /-- (A) mult by a 3-adic **unit** preserves parameter valuation. -/
  val_unit_smul : ∀ m : ℤ, ¬ (3 ∣ m) → ∀ z : M, val (m • z) = val z
  /-- (C) lower bound from `[3]z = 3z + z²·A(z)`, v(3)=3: `v([3]z) ≥ min{3+v(z), 2·v(z)}`. -/
  val_three_smul_ge : ∀ z : M, min (3 + val z) (2 * val z) ≤ val ((3 : ℤ) • z)
  /-- (B, PACKAGED) Ê₀(𝔪²) torsion-free ⇒ nonzero torsion has valuation exactly 1. -/
  torsion_val_eq_one :
    ∀ z : M, z ≠ 0 → (∃ n : ℕ, 0 < n ∧ n • z = 0) → val z = 1

attribute [instance] FormalKernel18.addCommGroup

namespace FormalKernel18
variable (FK : FormalKernel18)

lemma val_zero : FK.val 0 = ⊤ := (FK.val_eq_top 0).mpr rfl

/-- Lemma A: for 3∤m, [m] has no nonzero kernel on Ê₀(𝔪). -/
theorem no_prime_to_3_torsion (m : ℤ) (hm : ¬ (3 ∣ m)) :
    ∀ z : FK.M, m • z = 0 → z = 0 := by
  intro z hz
  by_contra hne
  have hval : FK.val (m • z) = FK.val z := FK.val_unit_smul m hm z
  rw [hz, FK.val_zero] at hval
  exact hne ((FK.val_eq_top z).mp hval.symm)

/-- Lemma C: any 3-power-torsion point is killed by [3]. -/
theorem three_power_torsion_exponent_three
    (z : FK.M) (k : ℕ) (hk : (3 ^ k) • z = 0) :
    (3 : ℤ) • z = 0 := by
  by_contra hne3
  have hzne : z ≠ 0 := by rintro rfl; exact hne3 (by simp)
  have hztor : ∃ n : ℕ, 0 < n ∧ n • z = 0 :=
    ⟨3 ^ k, pow_pos (by norm_num) k, hk⟩
  have h3tor : ∃ n : ℕ, 0 < n ∧ n • ((3 : ℤ) • z) = 0 := by
    refine ⟨3 ^ k, pow_pos (by norm_num) k, ?_⟩
    rw [smul_comm, hk, smul_zero]
  have hvz  : FK.val z = 1 := FK.torsion_val_eq_one z hzne hztor
  have hv3z : FK.val ((3 : ℤ) • z) = 1 := FK.torsion_val_eq_one _ hne3 h3tor
  have hge := FK.val_three_smul_ge z
  rw [hvz] at hge
  have h2 : (2 : ℕ∞) ≤ FK.val ((3 : ℤ) • z) :=
    le_trans (le_min (by norm_num) (by norm_num)) hge
  rw [hv3z] at h2
  exact absurd h2 (by decide)

section Assembly
variable {G : Type*} [AddCommGroup G]

/-- [21] annihilates the torsion of E₀(L). Rank-0 (upstream) then gives E₀(L)=ℤ/21. -/
theorem annihilated_by_21
    (hC : ∀ x : G, (∃ k : ℕ, ((3 : ℤ) ^ k) • x = 0) → (3 : ℤ) • x = 0)
    (hQ : ∀ x : G, (∃ j : ℤ, ¬ (3 ∣ j) ∧ j • x = 0) → (7 : ℤ) • x = 0)
    (x : G) (htor : ∃ n : ℕ, 0 < n ∧ n • x = 0) :
    (21 : ℤ) • x = 0 := by
  obtain ⟨n, hnpos, hnx⟩ := htor
  obtain ⟨a, k, hk3, hnk⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hnpos.ne' 3 (by norm_num)
  have hcop : IsCoprime ((3 : ℤ) ^ a) (k : ℤ) := by
    have h3k : IsCoprime (3 : ℤ) (k : ℤ) :=
      (Int.prime_three.coprime_iff_not_dvd).mpr (by exact_mod_cast hk3)
    simpa using h3k.pow_left
  obtain ⟨s, t, hst⟩ := hcop
  have hcast : ((n : ℤ)) • x = 0 := by
    have h := natCast_zsmul x n
    rw [h, hnx]
  have hnfac : ((n : ℤ)) = (3 : ℤ) ^ a * (k : ℤ) := by exact_mod_cast hnk
  set x' := (s * (3 : ℤ) ^ a) • x with hx'def
  set x₃ := (t * (k : ℤ)) • x with hx3def
  have hxsum : x' + x₃ = x := by
    rw [hx'def, hx3def, ← add_smul, hst, one_smul]
  have hx'7 : (7 : ℤ) • x' = 0 := by
    apply hQ
    refine ⟨(k : ℤ), by exact_mod_cast hk3, ?_⟩
    rw [hx'def, smul_smul,
        show (k : ℤ) * (s * (3 : ℤ) ^ a) = s * ((3 : ℤ) ^ a * (k : ℤ)) by ring,
        ← hnfac, mul_smul, hcast, smul_zero]
  have hx3C : (3 : ℤ) • x₃ = 0 := by
    apply hC
    refine ⟨a, ?_⟩
    rw [hx3def, smul_smul,
        show (3 : ℤ) ^ a * (t * (k : ℤ)) = t * ((3 : ℤ) ^ a * (k : ℤ)) by ring,
        ← hnfac, mul_smul, hcast, smul_zero]
  have e1 : (21 : ℤ) • x' = (3 : ℤ) • ((7 : ℤ) • x') := by
    rw [show (21 : ℤ) = 3 * 7 by norm_num, mul_smul]
  have e2 : (21 : ℤ) • x₃ = (7 : ℤ) • ((3 : ℤ) • x₃) := by
    rw [show (21 : ℤ) = 7 * 3 by norm_num, mul_smul]
  calc (21 : ℤ) • x
      = (21 : ℤ) • x' + (21 : ℤ) • x₃ := by rw [← smul_add, hxsum]
    _ = 0 := by rw [e1, e2, hx'7, hx3C, smul_zero, smul_zero, add_zero]

end Assembly
end FormalKernel18
