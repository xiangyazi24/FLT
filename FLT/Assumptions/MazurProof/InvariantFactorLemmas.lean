import Mathlib
import FLT.Assumptions.MazurProof.GroupTheory

/-!
# Rank lemmas for finite abelian group invariant factor decomposition

This file contains the key group-theory lemmas needed to prove
`finite_abelian_two_invariant_factors` in `Axioms.lean`.

The main results:
- `square_injection_of_two_divisible`: if two components of a direct sum
  `⨁ᵢ ℤ/nᵢ` are divisible by a prime `p`, then `(ℤ/p)²` injects into `G`.
- `cube_injection_of_three_divisible`: analogously for `(ℤ/p)³`.
- `at_most_one_p_component`: contrapositive — if `(ℤ/p)²` doesn't inject,
  at most one component is divisible by `p`.
- `at_most_two_2_components`: if `(ℤ/2)³` doesn't inject, at most two
  components are divisible by `2`.
-/

open scoped DirectSum

namespace MazurProof.InvariantFactorLemmas

variable {ι : Type*} [DecidableEq ι]

/--
If two components of `⨁ᵢ ℤ/nᵢ` are divisible by a prime `p`, then
`(ℤ/p)²` injects into `G ≃+ ⨁ᵢ ℤ/nᵢ`.

This is the forward direction of the rank constraint:
two `p`-divisible components ⇒ `p`-rank ≥ 2.
-/
theorem square_injection_of_two_divisible
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 1 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j : ι) (hij : i ≠ j)
    (hpi : (p : ℕ) ∣ n i) (hpj : (p : ℕ) ∣ n j) :
    ∃ f : ZMod p × ZMod p →+ G, Function.Injective f := by
  have hni : 0 < n i := by linarith [hn i]
  have hnj : 0 < n j := by linarith [hn j]
  obtain ⟨gi, hgi⟩ := MazurProof.zmod_contains_of_dvd p (n i) hp.pos hni hpi
  obtain ⟨gj, hgj⟩ := MazurProof.zmod_contains_of_dvd p (n j) hp.pos hnj hpj
  let fi := (DirectSum.of (fun k => ZMod (n k)) i).comp gi
  let fj := (DirectSum.of (fun k => ZMod (n k)) j).comp gj
  let f : ZMod p × ZMod p →+ ⨁ k : ι, ZMod (n k) :=
    { toFun := fun xy => fi xy.1 + fj xy.2
      map_zero' := by simp [fi, fj]
      map_add' := by intro x y; simp [fi, fj, Prod.fst_add, Prod.snd_add]; abel }
  have hf_inj : Function.Injective f := by
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    have h_eq : fi x₁ + fj x₂ = fi y₁ + fj y₂ := hxy
    have hi_eq : (fi x₁ + fj x₂) i = (fi y₁ + fj y₂) i := by rw [h_eq]
    have hj_eq : (fi x₁ + fj x₂) j = (fi y₁ + fj y₂) j := by rw [h_eq]
    simp only [fi, fj, AddMonoidHom.comp_apply, DirectSum.add_apply] at hi_eq hj_eq
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij, add_zero,
        DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij, add_zero] at hi_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same, zero_add] at hj_eq
    exact Prod.ext (hgi hi_eq) (hgj hj_eq)
  exact ⟨e.symm.toAddMonoidHom.comp f, e.symm.injective.comp hf_inj⟩

/--
If three components of `⨁ᵢ ℤ/nᵢ` are divisible by a prime `p`, then
`(ℤ/p)³` injects into `G ≃+ ⨁ᵢ ℤ/nᵢ`.
-/
theorem cube_injection_of_three_divisible
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 1 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hpi : (p : ℕ) ∣ n i) (hpj : (p : ℕ) ∣ n j) (hpk : (p : ℕ) ∣ n k) :
    ∃ f : ZMod p × ZMod p × ZMod p →+ G, Function.Injective f := by
  have hni : 0 < n i := by linarith [hn i]
  have hnj : 0 < n j := by linarith [hn j]
  have hnk : 0 < n k := by linarith [hn k]
  obtain ⟨gi, hgi⟩ := MazurProof.zmod_contains_of_dvd p (n i) hp.pos hni hpi
  obtain ⟨gj, hgj⟩ := MazurProof.zmod_contains_of_dvd p (n j) hp.pos hnj hpj
  obtain ⟨gk, hgk⟩ := MazurProof.zmod_contains_of_dvd p (n k) hp.pos hnk hpk
  let fi := (DirectSum.of (fun l => ZMod (n l)) i).comp gi
  let fj := (DirectSum.of (fun l => ZMod (n l)) j).comp gj
  let fk := (DirectSum.of (fun l => ZMod (n l)) k).comp gk
  let f : ZMod p × ZMod p × ZMod p →+ ⨁ l : ι, ZMod (n l) :=
    { toFun := fun xyz => fi xyz.1 + fj xyz.2.1 + fk xyz.2.2
      map_zero' := by simp [fi, fj, fk]
      map_add' := by intro x y; simp [fi, fj, fk, Prod.fst_add, Prod.snd_add]; abel }
  have hf_inj : Function.Injective f := by
    intro ⟨x₁, x₂, x₃⟩ ⟨y₁, y₂, y₃⟩ hxy
    have h_eq : fi x₁ + fj x₂ + fk x₃ = fi y₁ + fj y₂ + fk y₃ := hxy
    have hi_eq : (fi x₁ + fj x₂ + fk x₃) i = (fi y₁ + fj y₂ + fk y₃) i := by rw [h_eq]
    have hj_eq : (fi x₁ + fj x₂ + fk x₃) j = (fi y₁ + fj y₂ + fk y₃) j := by rw [h_eq]
    have hk_eq : (fi x₁ + fj x₂ + fk x₃) k = (fi y₁ + fj y₂ + fk y₃) k := by rw [h_eq]
    simp only [fi, fj, fk, AddMonoidHom.comp_apply, DirectSum.add_apply] at hi_eq hj_eq hk_eq
    rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij,
        DirectSum.of_eq_of_ne _ _ _ hik, add_zero, add_zero,
        DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ hij,
        DirectSum.of_eq_of_ne _ _ _ hik, add_zero, add_zero] at hi_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same,
        DirectSum.of_eq_of_ne _ _ _ hjk, zero_add, add_zero,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij), DirectSum.of_eq_same,
        DirectSum.of_eq_of_ne _ _ _ hjk, zero_add, add_zero] at hj_eq
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hik),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_same,
        zero_add, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hik),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_same,
        zero_add, zero_add] at hk_eq
    exact Prod.ext (hgi hi_eq) (Prod.ext (hgj hj_eq) (hgk hk_eq))
  exact ⟨e.symm.toAddMonoidHom.comp f, e.symm.injective.comp hf_inj⟩

/--
**Contrapositive of rank constraint.**
If `(ℤ/p)²` doesn't inject into `G`, then at most one component of the
primary decomposition is divisible by `p`.
-/
theorem at_most_one_p_component
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 1 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (p : ℕ) (hp : Nat.Prime p)
    (h_no_square : ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (i j : ι) (hij : i ≠ j)
    (hpi : (p : ℕ) ∣ n i) :
    ¬ (p : ℕ) ∣ n j :=
  fun hpj => h_no_square (square_injection_of_two_divisible G n hn e p hp i j hij hpi hpj)

/--
**2-rank constraint.**
If `(ℤ/2)³` doesn't inject into `G`, then at most two components of the
primary decomposition are divisible by `2`.
-/
theorem at_most_two_2_components
    (G : Type*) [AddCommGroup G]
    (n : ι → ℕ) (hn : ∀ i, 1 < n i)
    (e : G ≃+ ⨁ k : ι, ZMod (n k))
    (h_no_cube : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hpi : (2 : ℕ) ∣ n i) (hpj : (2 : ℕ) ∣ n j) :
    ¬ (2 : ℕ) ∣ n k :=
  fun hpk => h_no_cube (cube_injection_of_three_divisible G n hn e 2 (by norm_num)
    i j k hij hjk hik hpi hpj hpk)

end MazurProof.InvariantFactorLemmas
