# Q1909 (dm1): finite abelian group with bounded elementary subgroups

The intended route is not to reprove the finite abelian group theorem from scratch.  Use Mathlib's primary decomposition

```lean
AddCommGroup.equiv_directSum_zmod_of_finite G
```

which gives

```lean
G ≃+ ⨁ i : ι, ZMod (p i ^ e i)
```

with `ι` finite and `p i` prime.  Then prove two local obstruction lemmas:

1. if two nontrivial summands have the same odd prime `p`, then the two `p`-torsion generators give an injective
   `ZMod p × ZMod p →+ G`, contradicting the odd-prime hypothesis;
2. if three nontrivial summands have prime `2`, then the three order-two generators give an injective
   `ZMod 2 × ZMod 2 × ZMod 2 →+ G`, contradicting the second hypothesis.

The remaining finite bookkeeping is to put the surviving primary cyclic factors into two columns and collapse each column by CRT.  For an odd prime there is at most one factor, so put it in the second column.  For `p = 2` there are at most two factors; put the smaller exponent in the first column and the larger exponent in the second.  Then the first column order divides the second column order, and each column is a product of pairwise coprime prime powers, hence a single `ZMod` by CRT.

Here is the concrete Lean skeleton.  I have written the exact Mathlib declarations I would use; the `sorry`s are the remaining arithmetic/finite-combinatorics fill-ins.

```lean
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Tactic

open Function
open scoped DirectSum BigOperators Function

noncomputable section

namespace Q1909

/-!
API checkpoints used below:

* `AddCommGroup.equiv_directSum_zmod_of_finite G`
* `ZMod.lift` and `ZMod.lift_injective`
* `DirectSum.of`, `DirectSum.of_eq_same`, `DirectSum.of_eq_of_ne`
* `DirectSum.addEquivProd`
* binary CRT: `(ZMod.chineseRemainder h).symm.toAddEquiv`
* finite CRT: `(ZMod.prodEquivPi q hq).symm.toAddEquiv`
-/

/-- The order-`p` subgroup inside the cyclic `p`-primary group `ZMod (p^e)`.
It sends `1 : ZMod p` to `p^(e-1) : ZMod (p^e)`. -/
def zmodPrimeToPrimePow (p e : ℕ) (he : e ≠ 0) :
    ZMod p →+ ZMod (p ^ e) :=
  ZMod.lift p
    ⟨{ toFun := fun z : ℤ =>
          (z : ZMod (p ^ e)) * (p ^ (e - 1) : ZMod (p ^ e))
       map_zero' := by
          simp
       map_add' := by
          intro a b
          simp [Int.cast_add, add_mul] },
      by
        -- `p • p^(e-1) = p^e = 0` in `ZMod (p^e)`.
        rcases Nat.exists_eq_succ_of_ne_zero he with ⟨d, rfl⟩
        -- After rewriting, this is exactly `ZMod.natCast_self (p^(d+1))`.
        sorry⟩

lemma zmodPrimeToPrimePow_injective {p e : ℕ}
    (hp : p.Prime) (he : e ≠ 0) :
    Function.Injective (zmodPrimeToPrimePow p e he) := by
  -- This is the useful Mathlib reduction for maps out of `ZMod`.
  -- It reduces injectivity to the integer statement
  -- `z * p^(e-1) = 0` in `ZMod (p^e)` implies `(z : ZMod p) = 0`.
  dsimp [zmodPrimeToPrimePow]
  rw [ZMod.lift_injective]
  intro z hz
  -- Arithmetic core:
  -- from `p^e ∣ z * p^(e-1)` and `p.Prime`, with `e > 0`, get `p ∣ z`.
  -- Then `z` is zero in `ZMod p`.
  sorry

section TwoCoordinates

variable {ι : Type*} [DecidableEq ι]
variable (P E : ι → ℕ)

/-- If two primary summands have the same prime, map `ZMod p × ZMod p` into those two coordinates.
The domain is written as `ZMod (P i) × ZMod (P i)` and the second coordinate is moved to
`ZMod (P j)` by `ZMod.ringEquivCongr hP`. -/
def intoTwoCoordinates {i j : ι}
    (hP : P i = P j) (hei : E i ≠ 0) (hej : E j ≠ 0) :
    ZMod (P i) × ZMod (P i) →+ (⨁ k : ι, ZMod (P k ^ E k)) := by
  classical
  let β : ι → Type _ := fun k => ZMod (P k ^ E k)
  let ei : ZMod (P i) →+ β i :=
    zmodPrimeToPrimePow (P i) (E i) hei
  let castij : ZMod (P i) →+ ZMod (P j) :=
    ((ZMod.ringEquivCongr hP).toAddEquiv).toAddMonoidHom
  let ej : ZMod (P i) →+ β j :=
    (zmodPrimeToPrimePow (P j) (E j) hej).comp castij
  let fi : ZMod (P i) →+ (⨁ k : ι, β k) :=
    (DirectSum.of β i).comp ei
  let fj : ZMod (P i) →+ (⨁ k : ι, β k) :=
    (DirectSum.of β j).comp ej
  exact
    (fi.comp (AddMonoidHom.fst (ZMod (P i)) (ZMod (P i)))) +
      (fj.comp (AddMonoidHom.snd (ZMod (P i)) (ZMod (P i))))

lemma intoTwoCoordinates_injective {i j : ι}
    (hij : i ≠ j) (hP : P i = P j) (hp : (P i).Prime)
    (hei : E i ≠ 0) (hej : E j ≠ 0) :
    Function.Injective (intoTwoCoordinates P E hP hei hej) := by
  classical
  -- Evaluate the equality in coordinates `i` and `j`.
  -- `DirectSum.of_eq_same` recovers the chosen coordinate.
  -- `DirectSum.of_eq_of_ne` kills the other coordinate because `i ≠ j`.
  -- Then use `zmodPrimeToPrimePow_injective` in each coordinate.
  intro x y hxy
  ext <;> simp only [Prod.ext_iff]
  · -- first coordinate
    sorry
  · -- second coordinate
    sorry

end TwoCoordinates

section ForbiddenInjections

variable {G : Type*} [AddCommGroup G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P E : ι → ℕ}

lemma contradiction_of_two_same_odd_primary_components
    (Φ : G ≃+ (⨁ i : ι, ZMod (P i ^ E i)))
    (hOdd : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ ∃ f : (ZMod p × ZMod p) →+ G, Function.Injective f)
    {i j : ι} (hij : i ≠ j) (hP : P i = P j)
    (hp : (P i).Prime) (hp_odd : P i ≠ 2)
    (hei : E i ≠ 0) (hej : E j ≠ 0) : False := by
  classical
  let fD : ZMod (P i) × ZMod (P i) →+ (⨁ k : ι, ZMod (P k ^ E k)) :=
    intoTwoCoordinates P E hP hei hej
  have hfD : Function.Injective fD :=
    intoTwoCoordinates_injective P E hij hP hp hei hej
  let fG : ZMod (P i) × ZMod (P i) →+ G :=
    Φ.symm.toAddMonoidHom.comp fD
  have hfG : Function.Injective fG :=
    Φ.symm.injective.comp hfD
  exact (hOdd (P i) hp hp_odd) ⟨fG, hfG⟩

/-- The analogous three-coordinate map for `p = 2`.
This is the same construction as `intoTwoCoordinates`, repeated once more. -/
def intoThreeTwoCoordinates {P E : ι → ℕ} {i j k : ι}
    (hi : P i = 2) (hj : P j = 2) (hk : P k = 2)
    (hei : E i ≠ 0) (hej : E j ≠ 0) (hek : E k ≠ 0) :
    (ZMod 2 × ZMod 2 × ZMod 2) →+ (⨁ a : ι, ZMod (P a ^ E a)) := by
  classical
  -- Use `zmodPrimeToPrimePow 2 (E i) hei`, etc., compose with `DirectSum.of`,
  -- and add the three maps after precomposing with the three product projections.
  -- For the projections use `AddMonoidHom.fst`/`AddMonoidHom.snd` twice, according to
  -- the right-associated parsing of `α × β × γ`.
  sorry

lemma intoThreeTwoCoordinates_injective {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : P i = 2) (hj : P j = 2) (hk : P k = 2)
    (hei : E i ≠ 0) (hej : E j ≠ 0) (hek : E k ≠ 0) :
    Function.Injective (intoThreeTwoCoordinates (P := P) (E := E) hi hj hk hei hej hek) := by
  classical
  -- Same coordinatewise proof as the two-coordinate case.
  -- Use `DirectSum.of_eq_same` at `i`, `j`, `k`, and `DirectSum.of_eq_of_ne` off them.
  -- The one-coordinate injectivity is `zmodPrimeToPrimePow_injective Nat.prime_two`.
  sorry

lemma contradiction_of_three_two_primary_components
    (Φ : G ≃+ (⨁ i : ι, ZMod (P i ^ E i)))
    (hTwo : ¬ ∃ f : (ZMod 2 × ZMod 2 × ZMod 2) →+ G, Function.Injective f)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : P i = 2) (hj : P j = 2) (hk : P k = 2)
    (hei : E i ≠ 0) (hej : E j ≠ 0) (hek : E k ≠ 0) : False := by
  classical
  let fD : (ZMod 2 × ZMod 2 × ZMod 2) →+ (⨁ a : ι, ZMod (P a ^ E a)) :=
    intoThreeTwoCoordinates (P := P) (E := E) hi hj hk hei hej hek
  have hfD : Function.Injective fD :=
    intoThreeTwoCoordinates_injective (P := P) (E := E) hij hik hjk hi hj hk hei hej hek
  let fG : (ZMod 2 × ZMod 2 × ZMod 2) →+ G :=
    Φ.symm.toAddMonoidHom.comp fD
  have hfG : Function.Injective fG :=
    Φ.symm.injective.comp hfD
  exact hTwo ⟨fG, hfG⟩

end ForbiddenInjections

section CRTCollapse

/-- Collapse a finite direct sum of pairwise-coprime `ZMod (q i)` factors to one cyclic group.
This is the exact API spelling for the multi-factor CRT. -/
def directSumZModCRT {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hq : Pairwise (Nat.Coprime on q)) :
    (⨁ i : ι, ZMod (q i)) ≃+ ZMod (∏ i, q i) :=
  (DirectSum.addEquivProd (fun i : ι => ZMod (q i))).trans
    (ZMod.prodEquivPi q hq).symm.toAddEquiv

/-- Binary CRT, useful when the final two columns have coprime pieces assembled one at a time. -/
def binaryCRT (m n : ℕ) (h : m.Coprime n) :
    ZMod m × ZMod n ≃+ ZMod (m * n) :=
  (ZMod.chineseRemainder h).symm.toAddEquiv

end CRTCollapse

section MainStatement

/-- Finite bookkeeping lemma after the obstruction step.

Given the primary decomposition indices, if every odd prime occurs at most once and prime `2`
occurs at most twice, the summands can be partitioned into two CRT columns.  The first column
contains only the smaller `2`-power, while the second contains every odd-prime power and the larger
`2`-power.  Therefore the first column order divides the second. -/
lemma two_column_CRT_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E : ι → ℕ) (hP : ∀ i, (P i).Prime)
    (hmult : ∀ p : ℕ, p.Prime →
      (Finset.univ.filter fun i : ι => E i ≠ 0 ∧ P i = p).card ≤
        if p = 2 then 2 else 1) :
    ∃ m n : ℕ,
      m ∣ n ∧ Nonempty ((⨁ i : ι, ZMod (P i ^ E i)) ≃+ ZMod m × ZMod n) := by
  classical
  -- Construction outline:
  -- * discard the `E i = 0` factors, which are `ZMod 1` and hence subsingleton;
  -- * for every prime `p`, order its remaining exponents decreasingly;
  -- * put the largest exponent in column 2;
  -- * if `p = 2` and a second exponent exists, put that second exponent in column 1;
  -- * odd primes have no second exponent by `hmult`;
  -- * define `m` and `n` as the products of the column moduli;
  -- * prove pairwise coprimality in each column from distinct primes, using `Nat.Prime.coprime_iff_not_dvd`;
  -- * collapse each column with `directSumZModCRT`;
  -- * rearrange the direct sum by `DirectSum.equivCongrLeft`, `DirectSum.sigmaCurryEquiv`, and
  --   `DirectSum.addEquivProdDirectSum`.
  sorry

theorem finite_abelian_two_invariant_factors
    (G : Type*) [AddCommGroup G] [Finite G]
    (hOdd : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ ∃ f : (ZMod p × ZMod p) →+ G, Function.Injective f)
    (hTwo : ¬ ∃ f : (ZMod 2 × ZMod 2 × ZMod 2) →+ G, Function.Injective f) :
    ∃ m n : ℕ, m ∣ n ∧ Nonempty (G ≃+ ZMod m × ZMod n) := by
  classical
  obtain ⟨ι, hι, P, hP, E, ⟨Φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  classical
  letI : Fintype ι := hι
  have hmult : ∀ p : ℕ, p.Prime →
      (Finset.univ.filter fun i : ι => E i ≠ 0 ∧ P i = p).card ≤
        if p = 2 then 2 else 1 := by
    intro p hp
    by_cases hp2 : p = 2
    · -- If the filtered set had three different indices, use
      -- `contradiction_of_three_two_primary_components Φ hTwo`.
      subst hp2
      sorry
    · -- If the filtered set had two different indices, use
      -- `contradiction_of_two_same_odd_primary_components Φ hOdd`.
      sorry
  obtain ⟨m, n, hmn, ⟨Ψ⟩⟩ := two_column_CRT_form P E hP hmult
  exact ⟨m, n, hmn, ⟨Φ.trans Ψ⟩⟩

end MainStatement

end Q1909
```

The important parts that are already pinned to Mathlib API are:

```lean
obtain ⟨ι, hι, P, hP, E, ⟨Φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
```

for the primary decomposition, the torsion-generator embedding

```lean
ZMod.lift p ⟨_, _⟩
rw [ZMod.lift_injective]
```

for extracting `ZMod p` from a `ZMod (p^e)` component, coordinate insertion and recovery through

```lean
DirectSum.of β i
DirectSum.of_eq_same
DirectSum.of_eq_of_ne
```

and CRT collapse via

```lean
(DirectSum.addEquivProd (fun i => ZMod (q i))).trans
  (ZMod.prodEquivPi q hq).symm.toAddEquiv

(ZMod.chineseRemainder h).symm.toAddEquiv
```

The final `two_column_CRT_form` is deliberately isolated: it is only finite indexing, reindexing, and pairwise-coprime prime-power CRT, not group theory.  The group-theoretic obstruction is entirely in `contradiction_of_two_same_odd_primary_components` and `contradiction_of_three_two_primary_components`.
