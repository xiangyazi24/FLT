import Mathlib

set_option autoImplicit false

noncomputable section

namespace N15FormalSeparatedness

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A rational number integral at 2, expressed using `padicValRat`.
The disjunction is needed because Mathlib defines `padicValRat p 0 = 0`. -/
def TwoIntegral (q : ℚ) : Prop := q = 0 ∨ 0 ≤ padicValRat 2 q

lemma v2_two : padicValRat 2 (2 : ℚ) = 1 := by
  simpa using padicValRat.self (p := 2) (by decide)

/-- The elementary ultrametric estimate used by the formal-doubling argument. -/
lemma one_le_v2_two_add_mul
    {t u : ℚ}
    (ht : t ≠ 0)
    (hsum : 2 + t * u ≠ 0)
    (htv : 1 ≤ padicValRat 2 t)
    (hu : TwoIntegral u) :
    1 ≤ padicValRat 2 (2 + t * u) := by
  by_cases hu0 : u = 0
  · subst u
    simp [v2_two]
  have hvtu : 1 ≤ padicValRat 2 (t * u) := by
    rw [padicValRat.mul ht hu0]
    rcases hu with hu | hu
    · exact (hu0 hu).elim
    · omega
  have hadd := padicValRat.min_le_padicValRat_add (p := 2) hsum
  rw [v2_two] at hadd
  have hmin : min (1 : ℤ) (padicValRat 2 (t * u)) = 1 :=
    min_eq_left hvtu
  rw [hmin] at hadd
  exact hadd

/-- If an explicitly computed formal doubling parameter has the shape
`t(2P) = t(P) * (2 + t(P) * u) / d`, with `u` 2-integral and `d` a 2-adic
unit, then doubling raises the 2-adic valuation by at least one, provided the
double is not the identity. -/
lemma v2_formal_double_of_shape
    {t t₂ u d : ℚ}
    (hshape : t₂ = t * (2 + t * u) / d)
    (ht : t ≠ 0)
    (hsum : 2 + t * u ≠ 0)
    (hd : d ≠ 0)
    (htv : 1 ≤ padicValRat 2 t)
    (hu : TwoIntegral u)
    (hdv : padicValRat 2 d = 0) :
    padicValRat 2 t + 1 ≤ padicValRat 2 t₂ := by
  have hnum : t * (2 + t * u) ≠ 0 := mul_ne_zero ht hsum
  have hsumv := one_le_v2_two_add_mul ht hsum htv hu
  rw [hshape, padicValRat.div hnum hd, padicValRat.mul ht hsum, hdv]
  omega

/-- An element divisible by every power of two. -/
def InfinitelyTwoDivisible {G : Type*} [AddCommGroup G] (x : G) : Prop :=
  ∀ n : ℕ, ∃ y : G, (2 ^ n) • y = x

lemma twoPow_smul_succ {G : Type*} [AddCommGroup G] (n : ℕ) (x : G) :
    (2 ^ (n + 1)) • x = 2 • ((2 ^ n) • x) := by
  rw [pow_succ]
  exact mul_nsmul x (2 ^ n) 2

/-- The exact abstract interface supplied by a curve-specific formal-kernel construction.
The doubling estimate assumes `2 • P ≠ 0`, not merely `P ≠ 0`; this is
necessary at `p = 2`, where the formal kernel can contain nonzero 2-torsion. -/
structure LocalLayer (G : Type*) [AddCommGroup G] where
  formalKernel : AddSubgroup G
  parameter : G → ℚ
  four_mem : ∀ P : G, 4 • P ∈ formalKernel
  parameter_positive : ∀ P : G, P ∈ formalKernel → P ≠ 0 →
    1 ≤ padicValRat 2 (parameter P)
  double_valuation : ∀ P : G, P ∈ formalKernel → 2 • P ≠ 0 →
    padicValRat 2 (parameter P) + 1 ≤
      padicValRat 2 (parameter (2 • P))

variable {G : Type*} [AddCommGroup G]

/-- Curve-independent wrapper for the first requested lemma. -/
theorem n15_four_mul_mem_formalKernel
    (L : LocalLayer G) (P : G) :
    4 • P ∈ L.formalKernel :=
  L.four_mem P

/-- Corrected curve-independent wrapper for formal doubling. -/
theorem n15_v2_formal_double
    (L : LocalLayer G) (P : G)
    (hPker : P ∈ L.formalKernel) (h2P0 : 2 • P ≠ 0) :
    padicValRat 2 (L.parameter P) + 1 ≤
      padicValRat 2 (L.parameter (2 • P)) :=
  L.double_valuation P hPker h2P0

lemma v2_twoPow_smul
    (L : LocalLayer G) {P : G}
    (hPker : P ∈ L.formalKernel) :
    ∀ n : ℕ, (2 ^ n) • P ≠ 0 →
      padicValRat 2 (L.parameter P) + n ≤
        padicValRat 2 (L.parameter ((2 ^ n) • P)) := by
  intro n
  induction n with
  | zero =>
      intro
      simp
  | succ n ih =>
      intro hfinal
      have hprev0 : (2 ^ n) • P ≠ 0 := by
        intro hzero
        apply hfinal
        rw [twoPow_smul_succ, hzero]
        simp
      have hdouble0 : 2 • ((2 ^ n) • P) ≠ 0 := by
        rwa [← twoPow_smul_succ]
      have hprevKer : (2 ^ n) • P ∈ L.formalKernel :=
        L.formalKernel.nsmul_mem hPker (2 ^ n)
      have hstep := L.double_valuation ((2 ^ n) • P) hprevKer hdouble0
      have hind := ih hprev0
      rw [twoPow_smul_succ]
      omega

/-- The formal-kernel valuation estimate implies that the intersection of all
`2^n G` is trivial; no finite-generation hypothesis is used. -/
theorem n15_no_infinitely_two_divisible
    (L : LocalLayer G) (P : G)
    (hP : InfinitelyTwoDivisible P) :
    P = 0 := by
  by_contra hP0
  have hPker : P ∈ L.formalKernel := by
    rcases hP 2 with ⟨Q, hQ⟩
    have hfour := L.four_mem Q
    norm_num at hQ
    rwa [← hQ]
  have hvP : 1 ≤ padicValRat 2 (L.parameter P) :=
    L.parameter_positive P hPker hP0
  have hunbounded : ∀ n : ℕ, (n : ℤ) + 1 ≤ padicValRat 2 (L.parameter P) := by
    intro n
    rcases hP (n + 2) with ⟨Q, hQ⟩
    let R : G := 4 • Q
    have hRker : R ∈ L.formalKernel := by
      dsimp [R]
      exact L.four_mem Q
    have hPR : (2 ^ n) • R = P := by
      dsimp [R]
      calc
        (2 ^ n) • (4 • Q) = (2 ^ n * 4) • Q :=
          (mul_nsmul' Q (2 ^ n) 4).symm
        _ = (2 ^ (n + 2)) • Q := by norm_num [pow_add]
        _ = P := hQ
    have hR0 : R ≠ 0 := by
      intro hR
      apply hP0
      rw [← hPR, hR]
      simp
    have hfinal : (2 ^ n) • R ≠ 0 := by
      rw [hPR]
      exact hP0
    have hiter := v2_twoPow_smul L hRker n hfinal
    have hbase := L.parameter_positive R hRker hR0
    rw [hPR] at hiter
    omega
  have hvnonneg : 0 ≤ padicValRat 2 (L.parameter P) := by omega
  have hbad := hunbounded (padicValRat 2 (L.parameter P)).toNat
  have hcast : ((padicValRat 2 (L.parameter P)).toNat : ℤ) =
      padicValRat 2 (L.parameter P) :=
    Int.toNat_of_nonneg hvnonneg
  omega

/-- Iteration of a weak two-descent decomposition. -/
lemma iterated_decomposition
    (H : AddSubgroup G)
    (hstep : ∀ x : G, ∃ t : G, t ∈ H ∧ ∃ y : G, x = t + 2 • y)
    (x : G) :
    ∀ n : ℕ, ∃ t : G, t ∈ H ∧ ∃ y : G, x = t + (2 ^ n) • y := by
  intro n
  induction n with
  | zero =>
      exact ⟨0, H.zero_mem, x, by simp⟩
  | succ n ih =>
      rcases ih with ⟨s, hs, y, hy⟩
      rcases hstep y with ⟨t, ht, z, hz⟩
      refine ⟨s + (2 ^ n) • t, H.add_mem hs (H.nsmul_mem ht _), z, ?_⟩
      rw [hy, hz]
      simp only [nsmul_add, pow_succ, ← mul_nsmul']
      abel

lemma four_nsmul_infinitelyTwoDivisible
    (H : AddSubgroup G)
    (hstep : ∀ x : G, ∃ t : G, t ∈ H ∧ ∃ y : G, x = t + 2 • y)
    (hexp : ∀ t : G, t ∈ H → 4 • t = 0)
    (x : G) :
    InfinitelyTwoDivisible (4 • x) := by
  intro n
  rcases iterated_decomposition H hstep x n with ⟨t, ht, y, hy⟩
  refine ⟨4 • y, ?_⟩
  calc
    (2 ^ n) • (4 • y) = (2 ^ n * 4) • y :=
      (mul_nsmul' y (2 ^ n) 4).symm
    _ = (4 * 2 ^ n) • y := by rw [Nat.mul_comm]
    _ = 4 • ((2 ^ n) • y) := mul_nsmul' y 4 (2 ^ n)
    _ = 4 • (t + (2 ^ n) • y) := by
      simp [hexp t ht]
    _ = 4 • x := by rw [hy]

/-- Final weak-descent assembly once the corrected curve-specific local layer is built. -/
theorem four_nsmul_eq_zero_of_weakDescent
    (L : LocalLayer G)
    (H : AddSubgroup G)
    (hstep : ∀ x : G, ∃ t : G, t ∈ H ∧ ∃ y : G, x = t + 2 • y)
    (hexp : ∀ t : G, t ∈ H → 4 • t = 0)
    (x : G) :
    4 • x = 0 :=
  n15_no_infinitely_two_divisible L _
    (four_nsmul_infinitelyTwoDivisible H hstep hexp x)

end N15FormalSeparatedness
