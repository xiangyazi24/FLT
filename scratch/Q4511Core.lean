import Mathlib

set_option autoImplicit false

namespace Q4511Reference

/-- A strict `m`-divisibility filtration on an additive subgroup.  The level of zero is
irrelevant; strictness is required only when the `m`-multiple is nonzero. -/
structure StrictNSmulFiltration
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (m : ℕ) where
  level : H → ℕ
  strict : ∀ x : H, m • x ≠ 0 → level x < level (m • x)

namespace StrictNSmulFiltration

variable {G : Type*} [AddCommGroup G]
variable {H : AddSubgroup G} {m : ℕ}

lemma level_add_le_of_eq_pow_nsmul
    (F : StrictNSmulFiltration H m)
    {n : ℕ} {x y : H} (hx : x ≠ 0) (hxy : x = (m ^ n) • y) :
    F.level y + n ≤ F.level x := by
  induction n generalizing x with
  | zero =>
      simpa using (le_refl (F.level y))
  | succ n ih =>
      let z : H := (m ^ n) • y
      have hxz : x = m • z := by
        calc
          x = (m ^ (n + 1)) • y := hxy
          _ = (m * m ^ n) • y := by rw [pow_succ, Nat.mul_comm]
          _ = m • ((m ^ n) • y) := by rw [mul_nsmul]
          _ = m • z := rfl
      have hz : z ≠ 0 := by
        intro hz0
        apply hx
        rw [hxz, hz0, nsmul_zero]
      have hi : F.level y + n ≤ F.level z := ih hz rfl
      have hmz : m • z ≠ 0 := by
        intro hmz0
        exact hx (hxz.trans hmz0)
      have hs : F.level z < F.level x := by
        simpa [hxz] using F.strict z hmz
      omega

/-- A nonzero element cannot be divisible by every power of `m`. -/
theorem eq_zero_of_infinitely_divisible
    (F : StrictNSmulFiltration H m) (x : H)
    (hdiv : ∀ n : ℕ, ∃ y : H, x = (m ^ n) • y) :
    x = 0 := by
  by_contra hx
  obtain ⟨y, hy⟩ := hdiv (F.level x + 1)
  have hle := F.level_add_le_of_eq_pow_nsmul hx hy
  omega

end StrictNSmulFiltration

/-- Weak descent modulo a subgroup `T`: every point is a `T`-point plus an `m`-multiple. -/
structure WeakDescent
    {G : Type*} [AddCommGroup G] (m : ℕ) (T : AddSubgroup G) : Prop where
  decompose : ∀ x : G, ∃ t : T, ∃ y : G, x = (t : G) + m • y

namespace WeakDescent

variable {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
variable {T : AddSubgroup G}

lemma twentyOne_smul_torsion_zero
    (hT : ∀ t : T, (3 : ℕ) • (t : G) = 0) (t : T) :
    (21 : ℕ) • (t : G) = 0 := by
  rw [show (21 : ℕ) = 7 * 3 by norm_num, mul_nsmul, hT t, nsmul_zero]

lemma twentyOne_smul_three_pow_divisible
    (hweak : WeakDescent 3 T)
    (hT : ∀ t : T, (3 : ℕ) • (t : G) = 0)
    (n : ℕ) (x : G) :
    ∃ y : G, (21 : ℕ) • x = (3 ^ n) • ((21 : ℕ) • y) := by
  induction n with
  | zero =>
      exact ⟨x, by simp⟩
  | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨t, z, hz⟩ := hweak.decompose y
      refine ⟨z, ?_⟩
      have h21t : (21 : ℕ) • (t : G) = 0 := twentyOne_smul_torsion_zero hT t
      have hinner : (21 : ℕ) • ((t : G) + (3 : ℕ) • z) =
          (3 : ℕ) • ((21 : ℕ) • z) := by
        rw [nsmul_add, h21t, zero_add]
        simp only [smul_smul]
        congr 1
        norm_num
      calc
        (21 : ℕ) • x = (3 ^ n) • ((21 : ℕ) • y) := hy
        _ = (3 ^ n) • ((21 : ℕ) • ((t : G) + (3 : ℕ) • z)) := by rw [hz]
        _ = (3 ^ n) • ((3 : ℕ) • ((21 : ℕ) • z)) := by rw [hinner]
        _ = (3 ^ (n + 1)) • ((21 : ℕ) • z) := by
          rw [← mul_nsmul, pow_succ]

lemma twentyOne_smul_mem_ker
    (red : G →+ Q) (hred : ∀ q : Q, (7 : ℕ) • q = 0) (x : G) :
    red ((21 : ℕ) • x) = 0 := by
  rw [map_nsmul]
  calc
    (21 : ℕ) • red x = (3 : ℕ) • ((7 : ℕ) • red x) := by
      rw [show (21 : ℕ) = 3 * 7 by norm_num, mul_nsmul]
    _ = 0 := by rw [hred (red x), nsmul_zero]

/-- Weak `3`-descent modulo `3`-torsion, exponent `7` on the reduction,
and a strict `3`-filtration on the reduction kernel imply exponent `21`. -/
theorem twentyOne_annihilator
    (red : G →+ Q)
    (hweak : WeakDescent 3 T)
    (hT : ∀ t : T, (3 : ℕ) • (t : G) = 0)
    (hred : ∀ q : Q, (7 : ℕ) • q = 0)
    (F : StrictNSmulFiltration red.ker 3) :
    ∀ x : G, (21 : ℕ) • x = 0 := by
  intro x
  let X : red.ker := ⟨(21 : ℕ) • x, twentyOne_smul_mem_ker red hred x⟩
  have hdiv : ∀ n : ℕ, ∃ Y : red.ker, X = (3 ^ n) • Y := by
    intro n
    obtain ⟨y, hy⟩ := twentyOne_smul_three_pow_divisible hweak hT n x
    let Y : red.ker := ⟨(21 : ℕ) • y, twentyOne_smul_mem_ker red hred y⟩
    refine ⟨Y, ?_⟩
    apply Subtype.ext
    exact hy
  have hX : X = 0 := F.eq_zero_of_infinitely_divisible X hdiv
  exact congrArg Subtype.val hX

end WeakDescent

lemma min_three_add_two_mul_ge_succ {r : ℕ} (hr : 1 ≤ r) :
    r + 1 ≤ min (3 + r) (2 * r) := by
  omega

/-- The exact abstract interface produced by the local formal-parameter calculation. -/
structure FormalKernelThreeData
    {G Q : Type*} [AddCommGroup G] [AddCommGroup Q] (red : G →+ Q) where
  level : red.ker → ℕ
  level_pos : ∀ P : red.ker, P ≠ 0 → 1 ≤ level P
  three_bound : ∀ P : red.ker, (3 : ℕ) • P ≠ 0 →
    min (3 + level P) (2 * level P) ≤ level ((3 : ℕ) • P)

namespace FormalKernelThreeData

variable {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
variable {red : G →+ Q}

/-- The valuation estimate builds the strict `3`-filtration. -/
def strictNSmulFiltration (D : FormalKernelThreeData red) :
    StrictNSmulFiltration red.ker 3 where
  level := D.level
  strict := by
    intro P h3P
    have hP : P ≠ 0 := by
      intro hP0
      apply h3P
      rw [hP0, nsmul_zero]
    have hmin := min_three_add_two_mul_ge_succ (D.level_pos P hP)
    have hbound := D.three_bound P h3P
    omega

end FormalKernelThreeData

end Q4511Reference
