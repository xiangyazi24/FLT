import scratch.Q4221Core
import scratch.Q4221Valuation

set_option autoImplicit false

namespace N15FormalBackup

section ReductionKernel

variable {A : Type*} [AddCommGroup A]

/-- What `4P ∈ ker(red₂)` reduces to once a point-reduction homomorphism has
been supplied.  The pinned Mathlib has no such point-reduction map. -/
theorem n15_four_mul_mem_formalKernel
    (red : E0.Point →+ A)
    (hexp : ∀ Q : A, (4 : ℕ) • Q = 0)
    (hkernel : ∀ Q : E0.Point, FormalKernel Q ↔ red Q = 0)
    (P : E0.Point) : FormalKernel ((4 : ℕ) • P) := by
  rw [hkernel]
  rw [map_nsmul, hexp]

end ReductionKernel

section Separatedness

variable {G : Type*} [AddCommGroup G]

lemma iterate_level
    (L : ℕ → G → Prop)
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    {P : G} (hP : L 1 P) :
    ∀ n : ℕ, L (n + 1) ((2 ^ n : ℕ) • P) := by
  intro n
  induction n with
  | zero => simpa using hP
  | succ n ih =>
      have h := hraise (n + 1) ((2 ^ n : ℕ) • P) ih
      simpa [pow_succ', smul_smul, Nat.mul_assoc] using h

/-- Abstract, axiom-free separatedness lemma.  For the actual elliptic curve,
`L n P` is the nth formal filtration and `hfinite` follows from the finite
2-adic valuation of the fixed nonzero rational parameter `t(P)`. -/
theorem n15_no_infinitely_two_divisible
    (L : ℕ → G → Prop)
    (hfour : ∀ Q : G, L 1 ((4 : ℕ) • Q))
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    (hfinite : ∀ P : G, P ≠ 0 → ∃ B : ℕ, ¬ L (B + 1) P) :
    ∀ P : G, InfinitelyTwoDivisible P → P = 0 := by
  intro P hdiv
  by_contra hP0
  obtain ⟨B, hB⟩ := hfinite P hP0
  obtain ⟨Q, hQ⟩ := hdiv (B + 2)
  apply hB
  have hlev := iterate_level L hraise (n := B) (hfour Q)
  rw [hQ]
  simpa [smul_smul, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlev

end Separatedness

/-- Final group-theoretic assembly after the curve-specific Kummer and local
formal-filtration hypotheses have actually been proved. -/
theorem n15_weak_descent_final
    (H : AddSubgroup E0.Point)
    (hdecomp : ∀ P : E0.Point,
      ∃ h : H, ∃ Q : E0.Point, P = (h : E0.Point) + (2 : ℕ) • Q)
    (hexp : ∀ h : H, (4 : ℕ) • (h : E0.Point) = 0)
    (hsep : TwoAdicallySeparated E0.Point)
    (hfour : ∀ P : E0.Point, (4 : ℕ) • P = 0 → P ∈ H) :
    ∀ P : E0.Point, P ∈ H :=
  weak_descent_final H hdecomp hexp hsep hfour

end N15FormalBackup
