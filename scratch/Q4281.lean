import Mathlib

set_option autoImplicit false

namespace RankZeroAssembly

section DescentCore

variable {G : Type*} [AddCommGroup G]

/-- The weak-descent conclusion `G = H + 2G`. -/
def WeakDescent (H : AddSubgroup G) : Prop :=
  ∀ P : G, ∃ T : H, ∃ Q : G, P = (T : G) + (2 : ℕ) • Q

/-- Membership in every image of multiplication by a power of two. -/
def InfinitelyTwoDivisible (P : G) : Prop :=
  ∀ k : ℕ, ∃ Q : G, P = (2 ^ k : ℕ) • Q

/-- The separatedness input supplied by the formal-group argument. -/
def TwoAdicallySeparated (G : Type*) [AddCommGroup G] : Prop :=
  ∀ P : G, InfinitelyTwoDivisible P → P = 0

/-- Iterate `G = H + 2G` without any finite-generation hypothesis. -/
theorem iterated_decomposition
    (H : AddSubgroup G)
    (hweak : WeakDescent H)
    (P : G) :
    ∀ k : ℕ, ∃ T : H, ∃ Q : G,
      P = (T : G) + (2 ^ k : ℕ) • Q := by
  intro k
  induction k with
  | zero =>
      refine ⟨0, P, ?_⟩
      simp
  | succ k ih =>
      obtain ⟨T, Q, hPQ⟩ := ih
      obtain ⟨T', R, hQR⟩ := hweak Q
      refine ⟨T + (2 ^ k : ℕ) • T', R, ?_⟩
      rw [hPQ, hQR]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, nsmul_add, pow_succ,
        ← mul_nsmul]
      rw [Nat.mul_comm (2 ^ k) 2]
      abel

/-- If `m` annihilates `H`, then weak descent makes `m • P` infinitely
2-divisible for every `P`. -/
theorem annihilator_smul_infinitelyTwoDivisible
    (H : AddSubgroup G)
    (hweak : WeakDescent H)
    (m : ℕ)
    (hann : ∀ T : H, m • (T : G) = 0)
    (P : G) :
    InfinitelyTwoDivisible (m • P) := by
  intro k
  obtain ⟨T, Q, hPQ⟩ := iterated_decomposition H hweak P k
  refine ⟨m • Q, ?_⟩
  calc
    m • P = m • ((T : G) + (2 ^ k : ℕ) • Q) := by rw [hPQ]
    _ = m • (T : G) + m • ((2 ^ k : ℕ) • Q) := by rw [nsmul_add]
    _ = m • ((2 ^ k : ℕ) • Q) := by rw [hann, zero_add]
    _ = (2 ^ k : ℕ) • (m • Q) := by
      simp only [← mul_nsmul]
      rw [Nat.mul_comm]

/-- Weak descent plus 2-adic separatedness turns any annihilator of `H` into a
fixed annihilator of all of `G`. -/
theorem annihilator_smul_eq_zero
    (H : AddSubgroup G)
    (hweak : WeakDescent H)
    (m : ℕ)
    (hann : ∀ T : H, m • (T : G) = 0)
    (hsep : TwoAdicallySeparated G) :
    ∀ P : G, m • P = 0 := by
  intro P
  exact hsep (m • P)
    (annihilator_smul_infinitelyTwoDivisible H hweak m hann P)

/-- The form used for an eight-point subgroup of exponent dividing four. -/
theorem four_smul_eq_zero
    (H : AddSubgroup G)
    (hweak : WeakDescent H)
    (hann4 : ∀ T : H, (4 : ℕ) • (T : G) = 0)
    (hsep : TwoAdicallySeparated G) :
    ∀ P : G, (4 : ℕ) • P = 0 :=
  annihilator_smul_eq_zero H hweak 4 hann4 hsep

end DescentCore

section ReductionCardinality

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- Reduction is injective on the `m`-torsion subgroup. -/
def InjectiveOnNTorsion (m : ℕ) (red : G →+ A) : Prop :=
  ∀ P Q : G, m • P = 0 → m • Q = 0 → red P = red Q → P = Q

/-- Once all points are `m`-torsion, injective reduction into a finite group of
exactly the same cardinality as `H` forces every point to lie in `H`. -/
theorem all_mem_of_reduction_card
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (m : ℕ)
    (htors : ∀ P : G, m • P = 0)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion m red)
    (hcard : Fintype.card A = Fintype.card H) :
    ∀ P : G, P ∈ H := by
  have hinj : Function.Injective red := by
    intro P Q hPQ
    exact hred P Q (htors P) (htors Q) hPQ
  letI : Finite G := Finite.of_injective red hinj
  letI : Fintype G := Fintype.ofFinite G
  have hHG : Fintype.card H ≤ Fintype.card G := by
    exact Fintype.card_le_of_injective (fun T : H => (T : G)) Subtype.val_injective
  have hGA : Fintype.card G ≤ Fintype.card A := by
    exact Fintype.card_le_of_injective red hinj
  have hEq : Fintype.card G = Fintype.card H := by
    omega
  intro P
  by_contra hPH
  let f : Option H → G
    | none => P
    | some T => (T : G)
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            have hPb : P = (b : G) := by simpa [f] using hab
            exfalso
            apply hPH
            rw [hPb]
            exact b.property
    | some a =>
        cases b with
        | none =>
            have haP : (a : G) = P := by simpa [f] using hab
            exfalso
            apply hPH
            rw [← haP]
            exact a.property
        | some b =>
            have habv : (a : G) = (b : G) := by simpa [f] using hab
            have habs : a = b := Subtype.ext habv
            subst b
            rfl
  have hopt : Fintype.card (Option H) ≤ Fintype.card G :=
    Fintype.card_le_of_injective f hf
  have hbad : Fintype.card H + 1 ≤ Fintype.card H := by
    simpa [hEq] using hopt
  omega

/-- Equivalent subgroup formulation of `all_mem_of_reduction_card`. -/
theorem subgroup_eq_top_of_reduction_card
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (m : ℕ)
    (htors : ∀ P : G, m • P = 0)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion m red)
    (hcard : Fintype.card A = Fintype.card H) :
    H = ⊤ := by
  have hall := all_mem_of_reduction_card H m htors red hred hcard
  apply le_antisymm le_top
  intro P hP
  exact hall P

end ReductionCardinality

section CompleteAssembly

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]

/-- Reusable top-level theorem.  The hypotheses are exactly the three
curve-specific layers:

* `hweak`: two-isogeny/Kummer weak descent;
* `hsep`: formal-group 2-adic separatedness;
* `red`, `hred`, `hcard`: the good-prime torsion bound.
-/
theorem point_exhaustion
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (m : ℕ)
    (hweak : WeakDescent H)
    (hann : ∀ T : H, m • (T : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion m red)
    (hcard : Fintype.card A = Fintype.card H) :
    ∀ P : G, P ∈ H := by
  have htors : ∀ P : G, m • P = 0 :=
    annihilator_smul_eq_zero H hweak m hann hsep
  exact all_mem_of_reduction_card H m htors red hred hcard

/-- The exact exponent-four/cardinality-eight wrapper used by N15 and N21. -/
theorem point_exhaustion_four_eight
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (hweak : WeakDescent H)
    (hann4 : ∀ T : H, (4 : ℕ) • (T : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion 4 red)
    (hHcard : Fintype.card H = 8)
    (hAcard : Fintype.card A = 8) :
    ∀ P : G, P ∈ H := by
  apply point_exhaustion H 4 hweak hann4 hsep red hred
  omega

/-- Subgroup equality version of the complete assembly. -/
theorem subgroup_eq_top_four_eight
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (hweak : WeakDescent H)
    (hann4 : ∀ T : H, (4 : ℕ) • (T : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion 4 red)
    (hHcard : Fintype.card H = 8)
    (hAcard : Fintype.card A = 8) :
    H = ⊤ := by
  have hall := point_exhaustion_four_eight H hweak hann4 hsep red hred hHcard hAcard
  apply le_antisymm le_top
  intro P hP
  exact hall P

end CompleteAssembly

section ExplicitFinset

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A] [DecidableEq G]

/-- Final wrapper after a curve file identifies membership in `H` with the
explicit eight-point finset `S`. -/
theorem explicit_eight_points
    (H : AddSubgroup G)
    [Fintype H] [Fintype A]
    (S : Finset G)
    (hS : ∀ P : G, P ∈ H ↔ P ∈ S)
    (hweak : WeakDescent H)
    (hann4 : ∀ T : H, (4 : ℕ) • (T : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (red : G →+ A)
    (hred : InjectiveOnNTorsion 4 red)
    (hHcard : Fintype.card H = 8)
    (hAcard : Fintype.card A = 8) :
    ∀ P : G, P ∈ S := by
  intro P
  exact (hS P).mp
    (point_exhaustion_four_eight H hweak hann4 hsep red hred hHcard hAcard P)

end ExplicitFinset

end RankZeroAssembly
