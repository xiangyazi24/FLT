import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

/-- The good integral model used at `2`. -/
def E0 : WeierstrassCurve.Affine ℚ where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -5
  a₆ := 2

instance : E0.IsElliptic where
  isUnit := by
    rw [isUnit_iff_ne_zero]
    norm_num [E0, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma p2_on_E0 : E0.Equation (3 / 4 : ℚ) (-7 / 8 : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E0]

/-- The image on `E0` of the rational two-torsion point `(15,0)` on
`Y² = X(X-15)(X-16)`. -/
def P2 : E0.Point :=
  .some (3 / 4 : ℚ) (-7 / 8 : ℚ)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp p2_on_E0)

lemma P2_ne_zero : P2 ≠ 0 := by
  exact Point.some_ne_zero _

lemma P2_add_self : P2 + P2 = 0 := by
  apply Point.add_self_of_Y_eq
  norm_num [P2, E0, WeierstrassCurve.Affine.negY]

lemma two_smul_P2 : (2 : ℕ) • P2 = 0 := by
  simpa [two_nsmul] using P2_add_self

/-- The affine formal parameter `t=-x/y`, extended by `t(O)=0`. -/
def formalT : E0.Point → ℚ
  | 0 => 0
  | .some x y _ => -x / y

@[simp] lemma formalT_zero : formalT (0 : E0.Point) = 0 := rfl

lemma formalT_P2 : formalT P2 = 6 / 7 := by
  norm_num [formalT, P2]

lemma v2_formalT_P2 : padicValRat 2 (formalT P2) = 1 := by
  rw [formalT_P2]
  native_decide

/-- A deliberately minimal description of the first formal filtration.  The
zero point belongs to every filtration level. -/
def InFormalLevel (n : ℤ) (P : E0.Point) : Prop :=
  P = 0 ∨ formalT P ≠ 0 ∧ n ≤ padicValRat 2 (formalT P)

abbrev FormalKernel (P : E0.Point) : Prop := InFormalLevel 1 P

lemma P2_mem_formalKernel : FormalKernel P2 := by
  right
  constructor
  · rw [formalT_P2]
    norm_num
  · rw [v2_formalT_P2]

/-- The proposed finite-valued statement is false: `P2` is a nonzero point in
    the formal kernel, while `2P2=O`, and Mathlib defines
    `padicValRat 2 0 = 0`. -/
theorem proposed_n15_v2_formal_double_is_false :
    ¬ (∀ P : E0.Point, FormalKernel P → P ≠ 0 →
        padicValRat 2 (formalT ((2 : ℕ) • P)) ≥
          padicValRat 2 (formalT P) + 1) := by
  intro h
  have bad := h P2 P2_mem_formalKernel P2_ne_zero
  rw [two_smul_P2, formalT_zero, v2_formalT_P2] at bad
  norm_num [padicValRat] at bad

/-- Correct filtration form of the doubling estimate.  It treats `O` as
    belonging to every level, exactly as the extended valuation `v(0)=∞`
    would. -/
def FormalDoublingRaises : Prop :=
  ∀ (n : ℤ) (P : E0.Point), 1 ≤ n → InFormalLevel n P →
    InFormalLevel (n + 1) ((2 : ℕ) • P)

section AbstractWeakDescent

variable {G : Type*} [AddCommGroup G]

/-- Membership in every image of multiplication by a power of two. -/
def InfinitelyTwoDivisible (x : G) : Prop :=
  ∀ n : ℕ, ∃ y : G, x = (2 ^ n : ℕ) • y

/-- The separatedness statement needed after local formal-group analysis. -/
def TwoAdicallySeparated (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, InfinitelyTwoDivisible x → x = 0

/-- Iteration of `G = H + 2G`.  The weighted sum of representatives is folded
    back into the subgroup `H`, so the statement stays small. -/
theorem iterated_decomposition (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (x : G) :
    ∀ n : ℕ, ∃ h : H, ∃ y : G, x = (h : G) + (2 ^ n : ℕ) • y := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, x, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨h, y, hxy⟩ := ih
      obtain ⟨h', z, hyz⟩ := hdecomp y
      refine ⟨h + (2 ^ n : ℕ) • h', z, ?_⟩
      rw [hxy, hyz]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, nsmul_add, pow_succ,
        ← mul_nsmul]
      rw [Nat.mul_comm (2 ^ n) 2]
      abel

/-- Multiplying by four removes all subgroup representatives.  Hence every
    `4x` is infinitely two-divisible. -/
theorem four_mul_infinitelyTwoDivisible (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (hexp : ∀ h : H, (4 : ℕ) • (h : G) = 0)
    (x : G) : InfinitelyTwoDivisible ((4 : ℕ) • x) := by
  intro n
  obtain ⟨h, y, hxy⟩ := iterated_decomposition H hdecomp x n
  refine ⟨(4 : ℕ) • y, ?_⟩
  calc
    (4 : ℕ) • x = (4 : ℕ) • ((h : G) + (2 ^ n : ℕ) • y) := by rw [hxy]
    _ = (4 : ℕ) • (h : G) + (4 : ℕ) • ((2 ^ n : ℕ) • y) := by rw [nsmul_add]
    _ = (4 : ℕ) • ((2 ^ n : ℕ) • y) := by rw [hexp, zero_add]
    _ = (2 ^ n : ℕ) • ((4 : ℕ) • y) := by
      simp only [← mul_nsmul]
      rw [Nat.mul_comm]

/-- The exact group-theoretic final assembly used by the N15 argument. -/
theorem weak_descent_final (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (hexp : ∀ h : H, (4 : ℕ) • (h : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (hfour : ∀ x : G, (4 : ℕ) • x = 0 → x ∈ H) :
    ∀ x : G, x ∈ H := by
  intro x
  apply hfour x
  apply hsep
  exact four_mul_infinitelyTwoDivisible H hdecomp hexp x

end AbstractWeakDescent

end N15FormalBackup
