import Mathlib

set_option autoImplicit false

namespace NoInfiniteTwoDivisibility

section Core

variable {G : Type*} [AddCommGroup G]

/-- `H` has exponent dividing `e`: every element of `H` is killed by `e`. -/
def HasExponent (H : AddSubgroup G) (e : ℕ) : Prop :=
  ∀ t : H, e • (t : G) = 0

/-- The weak two-descent conclusion `G = H + 2G`. -/
def WeakTwoDescent (H : AddSubgroup G) : Prop :=
  ∀ x : G, ∃ t : H, ∃ y : G, x = (t : G) + (2 : ℕ) • y

/-- An element lying in `2^n G` for every `n`. -/
def InfinitelyTwoDivisible (x : G) : Prop :=
  ∀ n : ℕ, ∃ q : G, (2 ^ n : ℕ) • q = x

/-- The intersection of all subgroups `2^n G` is trivial. -/
def TwoAdicallySeparated (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, InfinitelyTwoDivisible x → x = 0

/-- Iteration of weak descent: for every `n`, write
`x = tₙ + 2^n • yₙ` with `tₙ ∈ H`. -/
theorem iterated_decomposition
    (H : AddSubgroup G)
    (hweak : WeakTwoDescent H)
    (x : G) :
    ∀ n : ℕ, ∃ t : H, ∃ y : G,
      x = (t : G) + (2 ^ n : ℕ) • y := by
  intro n
  induction n with
  | zero =>
      exact ⟨0, x, by simp⟩
  | succ n ih =>
      obtain ⟨s, y, hxy⟩ := ih
      obtain ⟨t, z, hyz⟩ := hweak y
      refine ⟨s + (2 ^ n : ℕ) • t, z, ?_⟩
      rw [hxy, hyz]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, nsmul_add, pow_succ,
        ← mul_nsmul]
      rw [Nat.mul_comm (2 ^ n) 2]
      abel

/-- If `e` annihilates the weak-descent subgroup `H`, then `e • x` is divisible
by every power of two. -/
theorem e_nsmul_infinitelyTwoDivisible
    (H : AddSubgroup G)
    (e : ℕ)
    (hweak : WeakTwoDescent H)
    (hexp : HasExponent H e)
    (x : G) :
    InfinitelyTwoDivisible (e • x) := by
  intro n
  obtain ⟨t, y, hxy⟩ := iterated_decomposition H hweak x n
  refine ⟨e • y, ?_⟩
  calc
    (2 ^ n : ℕ) • (e • y) = e • ((2 ^ n : ℕ) • y) := by
      simp only [← mul_nsmul]
      rw [Nat.mul_comm]
    _ = e • ((t : G) + (2 ^ n : ℕ) • y) := by
      rw [nsmul_add, hexp t, zero_add]
    _ = e • x := by rw [hxy]

/-- The specialization most often used for the eight-point elliptic-curve
subgroups, whose exponent divides four. -/
theorem four_nsmul_infinitelyTwoDivisible
    (H : AddSubgroup G)
    (hweak : WeakTwoDescent H)
    (hexp4 : ∀ t : H, (4 : ℕ) • (t : G) = 0)
    (x : G) :
    InfinitelyTwoDivisible ((4 : ℕ) • x) :=
  e_nsmul_infinitelyTwoDivisible H 4 hweak hexp4 x

/-- **Dimension-free rank-zero assembly.** Weak two-descent, an exponent bound
on the representatives, and two-adic separatedness imply the same exponent
bound on the whole group. No finite-generation hypothesis is used. -/
theorem exponent_of_weakTwoDescent_of_separated
    (H : AddSubgroup G)
    (e : ℕ)
    (hweak : WeakTwoDescent H)
    (hexp : HasExponent H e)
    (hsep : TwoAdicallySeparated G) :
    ∀ x : G, e • x = 0 := by
  intro x
  exact hsep (e • x)
    (e_nsmul_infinitelyTwoDivisible H e hweak hexp x)

/-- The preceding theorem with exactly the hypotheses written out, rather than
through the named predicates. -/
theorem no_infinite_two_divisibility_implies_exponent
    (H : AddSubgroup G)
    (e : ℕ)
    (hexp : ∀ t : H, e • (t : G) = 0)
    (hweak : ∀ x : G, ∃ t : H, ∃ y : G,
      x = (t : G) + (2 : ℕ) • y)
    (hsep : ∀ x : G,
      (∀ n : ℕ, ∃ q : G, (2 ^ n : ℕ) • q = x) → x = 0) :
    ∀ x : G, e • x = 0 :=
  exponent_of_weakTwoDescent_of_separated H e hweak hexp hsep

end Core

section FiniteReduction

variable {G F : Type*} [AddCommGroup G] [AddCommGroup F]

/-- A homomorphism is injective on the subgroup of elements killed by `e`. -/
def InjectiveOnETorsion (e : ℕ) (f : G →+ F) : Prop :=
  ∀ x y : G, e • x = 0 → e • y = 0 → f x = f y → x = y

/-- Once every element of `G` is killed by `e`, injectivity on `e`-torsion is
ordinary injectivity. -/
theorem hom_injective_of_all_e_torsion
    (e : ℕ)
    (hall : ∀ x : G, e • x = 0)
    (f : G →+ F)
    (hinj : InjectiveOnETorsion e f) :
    Function.Injective f := by
  intro x y hxy
  exact hinj x y (hall x) (hall y) hxy

/-- Good-prime reduction into a finite target bounds the cardinality of `G`.
The `Finite G` instance is obtained from the injection; it is not assumed. -/
theorem natCard_le_finite_target
    [Finite F]
    (H : AddSubgroup G)
    (e : ℕ)
    (hweak : WeakTwoDescent H)
    (hexp : HasExponent H e)
    (hsep : TwoAdicallySeparated G)
    (f : G →+ F)
    (hinj : InjectiveOnETorsion e f) :
    Nat.card G ≤ Nat.card F := by
  have hall : ∀ x : G, e • x = 0 :=
    exponent_of_weakTwoDescent_of_separated H e hweak hexp hsep
  have hf : Function.Injective f :=
    hom_injective_of_all_e_torsion e hall f hinj
  exact Nat.card_le_card_of_injective (f : G → F) hf

/-- Image-cardinality version. If the image of the reduction map has cardinality
`N`, then `G` has cardinality at most `N`. Under the hypotheses the map is in
fact injective on all of `G`, so equality also follows, but the stated bound is
the form normally consumed by point-exhaustion arguments. -/
theorem natCard_le_image
    [Finite F]
    (H : AddSubgroup G)
    (e : ℕ)
    (hweak : WeakTwoDescent H)
    (hexp : HasExponent H e)
    (hsep : TwoAdicallySeparated G)
    (f : G →+ F)
    (hinj : InjectiveOnETorsion e f)
    (N : ℕ)
    (himage : Nat.card (Set.range (f : G → F)) = N) :
    Nat.card G ≤ N := by
  have hall : ∀ x : G, e • x = 0 :=
    exponent_of_weakTwoDescent_of_separated H e hweak hexp hsep
  have hf : Function.Injective f :=
    hom_injective_of_all_e_torsion e hall f hinj
  let toImage : G → Set.range (f : G → F) :=
    fun x => ⟨f x, ⟨x, rfl⟩⟩
  have htoImage : Function.Injective toImage := by
    intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  calc
    Nat.card G ≤ Nat.card (Set.range (f : G → F)) :=
      Nat.card_le_card_of_injective toImage htoImage
    _ = N := himage

end FiniteReduction

end NoInfiniteTwoDivisibility
