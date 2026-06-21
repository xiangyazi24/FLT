# Q65 dm4 — base `ℙ¹(ℚ)` Northcott for primitive integer representatives

This is the clean assembly lemma for the A6 height route.  The primitive condition is not used for finiteness; the proof only uses the two integral coordinates and `not_both_zero` for `mulHeight_pos`/`mulHeight ≥ 1`.

The finite-height set injects into the finite integer box

```lean
Finset.Icc (-(N : ℤ)) (N : ℤ) × Finset.Icc (-(N : ℤ)) (N : ℤ)
```

by sending `x` to `(x.X, x.Z)`.  For the logarithmic version, `Real.log H ≤ B` gives `H ≤ Real.exp B` by `le_exp_of_log_le`; then `Real.exp B ≤ Nat.ceil (Real.exp B)` by `Nat.le_ceil`.

```lean
import Mathlib

open scoped BigOperators

/-- Primitive integral representatives for `ℙ¹(ℚ)`. -/
structure P1Q where
  X : ℤ
  Z : ℤ
  prim : IsCoprime X Z
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1Q

/-- Multiplicative height of a primitive integral representative of a rational point of `ℙ¹`. -/
def mulHeight (x : P1Q) : ℕ :=
  max x.X.natAbs x.Z.natAbs

/-- Logarithmic height of a primitive integral representative of a rational point of `ℙ¹`. -/
noncomputable def logHeight (x : P1Q) : ℝ :=
  Real.log (x.mulHeight : ℝ)

lemma mulHeight_pos (x : P1Q) : 0 < x.mulHeight := by
  dsimp [mulHeight]
  rcases x.not_both_zero with hX | hZ
  · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hX) (le_max_left _ _)
  · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hZ) (le_max_right _ _)

lemma one_le_mulHeight (x : P1Q) : 1 ≤ x.mulHeight :=
  Nat.succ_le_of_lt (mulHeight_pos x)

/-- The finite integer interval used for the Northcott box. -/
abbrev intBox (N : ℕ) : Type :=
  {z : ℤ // z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}

private lemma mem_intBox_of_natAbs_le {N : ℕ} {z : ℤ} (hz : z.natAbs ≤ N) :
    z ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  rw [Finset.mem_Icc]
  have hN : (z.natAbs : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hz
  constructor
  · have hneg : -(N : ℤ) ≤ -((z.natAbs : ℤ)) := neg_le_neg hN
    exact le_trans hneg (Int.neg_natAbs_le z)
  · exact le_trans (Int.le_natAbs z) hN

private noncomputable def toBox (N : ℕ)
    (x : {x : P1Q // x.mulHeight ≤ N}) : intBox N × intBox N :=
  (⟨x.1.X, mem_intBox_of_natAbs_le (N := N) (z := x.1.X) <| by
      exact le_trans (le_max_left x.1.X.natAbs x.1.Z.natAbs) (by
        simpa [mulHeight] using x.2)⟩,
   ⟨x.1.Z, mem_intBox_of_natAbs_le (N := N) (z := x.1.Z) <| by
      exact le_trans (le_max_right x.1.X.natAbs x.1.Z.natAbs) (by
        simpa [mulHeight] using x.2)⟩)

private lemma toBox_injective (N : ℕ) :
    Function.Injective (toBox N) := by
  intro x y hxy
  apply Subtype.ext
  ext
  · exact congrArg (fun q : intBox N × intBox N => (q.1 : ℤ)) hxy
  · exact congrArg (fun q : intBox N × intBox N => (q.2 : ℤ)) hxy

private theorem boundedSubtype_finite (N : ℕ) :
    Finite {x : P1Q // x.mulHeight ≤ N} := by
  classical
  haveI : Fintype (intBox N) := by
    dsimp [intBox]
    infer_instance
  haveI : Finite (intBox N × intBox N) := inferInstance
  exact Finite.of_injective (toBox N) (toBox_injective N)

/-- Northcott for the natural multiplicative height on primitive integral `ℙ¹(ℚ)` reps. -/
theorem mulHeight_northcott_nat (N : ℕ) :
    {x : P1Q | x.mulHeight ≤ N}.Finite := by
  classical
  haveI : Finite {x : P1Q // x.mulHeight ≤ N} := boundedSubtype_finite N
  let f : {x : P1Q // x.mulHeight ≤ N} → P1Q := fun x => x.1
  have hfin : (Set.univ : Set {x : P1Q // x.mulHeight ≤ N}).Finite := Set.finite_univ
  have himage : f '' Set.univ = {x : P1Q | x.mulHeight ≤ N} := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [← himage]
  exact hfin.image f

/-- Northcott for the logarithmic height on primitive integral `ℙ¹(ℚ)` reps. -/
theorem logHeight_northcott (B : ℝ) :
    {x : P1Q | P1Q.logHeight x ≤ B}.Finite := by
  classical
  let N : ℕ := Nat.ceil (Real.exp B)
  exact (mulHeight_northcott_nat N).subset ?_
  intro x hx
  change x.mulHeight ≤ N
  have hxlog : Real.log (x.mulHeight : ℝ) ≤ B := by
    simpa [P1Q.logHeight] using hx
  have hHexp : (x.mulHeight : ℝ) ≤ Real.exp B :=
    le_exp_of_log_le hxlog
  have hexpceil : Real.exp B ≤ (N : ℝ) := by
    simpa [N] using Nat.le_ceil (Real.exp B)
  have hHceil : (x.mulHeight : ℝ) ≤ (N : ℝ) :=
    le_trans hHexp hexpceil
  exact_mod_cast hHceil

end P1Q
```

## API notes / possible local-name adjustments

The proof above is written against current Mathlib-style names.  If the project pin uses a slightly older alias, the only likely edits are local:

```lean
Int.neg_natAbs_le z
Int.le_natAbs z
Nat.le_ceil (Real.exp B)
le_exp_of_log_le hxlog
```

If `Nat.le_ceil` is named differently in the pin, replace the line

```lean
simpa [N] using Nat.le_ceil (Real.exp B)
```

by the local theorem giving `Real.exp B ≤ (Nat.ceil (Real.exp B) : ℝ)`.  If the two `Int` lemmas are unavailable, replace `mem_intBox_of_natAbs_le` by a `simpa [Finset.mem_Icc, Int.natAbs_le] using hz` proof, provided the pin exposes the `Int.natAbs_le` iff lemma.
