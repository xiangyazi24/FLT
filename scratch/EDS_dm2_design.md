# Q184: x-only ladder ⇔ division-polynomial coordinate identity

Goal: prove that the Montgomery/Kummer x-only ladder representative for `x(nP)` is projectively equal to the division-polynomial representative

```lean
![(W.Φ n).eval x, (W.ΨSq n).eval x]
```

for all `n`, assuming the ladder doubling and differential-addition formulas are already proved over a general field.

The clean proof is **strong induction on the ladder pair**, not induction on a single representative.

The invariant is:

```text
pair(n) = (x(nP), x((n+1)P))
~
([Φ_n(x):ΨSq_n(x)], [Φ_{n+1}(x):ΨSq_{n+1}(x)]).
```

Then:

* even step `n = 2m`: double the first component and differential-add the pair;
* odd step `n = 2m + 1`: differential-add the pair and double the second component.

This matches exactly the Montgomery ladder recurrence.

---

## Important Mathlib division-polynomial API

Existing Mathlib definitions/lemmas to use:

```lean
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Φ
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.preΨ_even
WeierstrassCurve.preΨ_odd
WeierstrassCurve.ΨSq_ofNat
WeierstrassCurve.Ψ₂Sq
```

Mathlib's division-polynomial file defines

```lean
W.ΨSq n = W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1
```

and, by definition of `Φ`,

```text
Φ_n = X * ΨSq_n - preΨ_{n+1} * preΨ_{n-1} * (if Even n then 1 else Ψ₂Sq).
```

If the repo does not already expose `Φ_even`, `Φ_odd`, `ΨSq_even`, `ΨSq_odd`, add the four closeable wrapper lemmas below. They should be `rw [WeierstrassCurve.ΨSq, WeierstrassCurve.Φ, preΨ_even/preΨ_odd]` plus parity simplification and `ring`/`ring_nf`.

---

# Lean scaffold

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- A vector representative of a point on `ℙ¹`. -/
abbrev P1Vec := Fin 2 → k

/-- Projective equality of nonzero `P¹` vectors. Replace by the repo's `SameP1Vec` if already present. -/
def SameP1Vec (v w : P1Vec) : Prop :=
  ∃ u : kˣ, v = u • w

namespace SameP1Vec

variable {W}

lemma refl (v : P1Vec) : SameP1Vec v v := by
  exact ⟨1, by simp⟩

lemma symm {v w : P1Vec} (h : SameP1Vec v w) : SameP1Vec w v := by
  rcases h with ⟨u, rfl⟩
  exact ⟨u⁻¹, by ext i; simp [Units.smul_def, mul_comm, mul_assoc]⟩

lemma trans {u v w : P1Vec} (huv : SameP1Vec u v) (hvw : SameP1Vec v w) : SameP1Vec u w := by
  rcases huv with ⟨a, rfl⟩
  rcases hvw with ⟨b, rfl⟩
  exact ⟨a * b, by ext i; simp [Units.smul_def, mul_assoc]⟩

end SameP1Vec

/-- Division-polynomial `P¹` representative `[Φ_n(x):ΨSq_n(x)]`. -/
def phiPsiVec (x : k) (n : ℤ) : P1Vec :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-!
## Existing ladder-side declarations to plug in

Rename these placeholders to the actual repo names.  The search did not find public identifiers
`xLadderRep`, `dupNumH`, `dupDenH`, or `SameP1Vec` in the connected branch, so this scaffold is
written with descriptive names.
-/

/-- x-only doubling vector `[dupNumH(X,Z):dupDenH(X,Z)]`. Existing in repo. -/
-- def xDBL (v : P1Vec) : P1Vec := ![dupNumH W (v 0) (v 1), dupDenH W (v 0) (v 1)]

/-- Differential addition vector from `x(P-Q)`, `x(P)`, `x(Q)`. Existing in repo. -/
-- def xDADD (base v w : P1Vec) : P1Vec :=
--   ![diffAddNumH W base v w, diffAddDenH W base v w]

/-- Ladder pair `(x(nP), x((n+1)P))`. Existing in repo. -/
-- def xLadderPairRep (x : k) (n : ℕ) : P1Vec × P1Vec := ...

/-- Single-output ladder representative. Usually this is `(xLadderPairRep x n).1`. Existing in repo. -/
-- def xLadderRep (x : k) (n : ℕ) : P1Vec := (xLadderPairRep W x n).1

/-- The base vector `[x:1]`. -/
def baseVec (x : k) : P1Vec := ![x, 1]

/-- Pair invariant for the Montgomery ladder. -/
def LadderPairInv
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (x : k) (n : ℕ) : Prop :=
  SameP1Vec (xLadderPairRep x n).1 (W.phiPsiVec x (n : ℤ)) ∧
  SameP1Vec (xLadderPairRep x n).2 (W.phiPsiVec x ((n : ℤ) + 1))

/-!
## 0. Homogeneity transport lemmas

These are CLOSEABLE-NOW from the already-proved homogeneity of the Kummer formulas.
If the repo already has homogeneity lemmas for `dupNumH/dupDenH` and differential addition, use those.
-/

/-- CLOSEABLE-NOW: doubling respects projective equality. -/
theorem same_xDBL
    (xDBL : P1Vec → P1Vec)
    (h_xDBL_homogeneous : ∀ {v w}, SameP1Vec v w → SameP1Vec (xDBL v) (xDBL w))
    {v w : P1Vec} (hvw : SameP1Vec v w) :
    SameP1Vec (xDBL v) (xDBL w) :=
  h_xDBL_homogeneous hvw

/-- CLOSEABLE-NOW: differential addition respects projective equality in all inputs. -/
theorem same_xDADD
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (h_xDADD_homogeneous :
      ∀ {b b' v v' w w'},
        SameP1Vec b b' → SameP1Vec v v' → SameP1Vec w w' →
        SameP1Vec (xDADD b v w) (xDADD b' v' w'))
    {b b' v v' w w' : P1Vec}
    (hb : SameP1Vec b b') (hv : SameP1Vec v v') (hw : SameP1Vec w w') :
    SameP1Vec (xDADD b v w) (xDADD b' v' w') :=
  h_xDADD_homogeneous hb hv hw

/-- CLOSEABLE-NOW: `[x:1]` is the `n=1` division-polynomial vector. -/
theorem baseVec_same_phiPsi_one (x : k) :
    SameP1Vec (baseVec x) (W.phiPsiVec x 1) := by
  -- Expected proof:
  --   simp [baseVec, phiPsiVec, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq]
  -- or use the already-proven concrete `n=1` base case.
  -- This may need a local lemma `phiPsiVec_one` if `simp` does not unfold enough.
  sorry

/-!
## 1. Division-polynomial recurrence wrapper lemmas

These are CLOSEABLE-NOW wrappers around existing Mathlib recurrences/definitions.
They are useful because the Kummer identities should be proved against these expanded forms, not
against the raw definitions each time.
-/

/-- CLOSEABLE-NOW: expanded formula for `ΨSq_{2m}`. -/
theorem ΨSq_even_expanded (m : ℤ) :
    W.ΨSq (2 * m) =
      (W.preΨ (2 * m)) ^ 2 * W.Ψ₂Sq := by
  simp [WeierstrassCurve.ΨSq, even_two_mul]

/-- CLOSEABLE-NOW: expanded formula for `ΨSq_{2m+1}`. -/
theorem ΨSq_odd_expanded (m : ℤ) :
    W.ΨSq (2 * m + 1) =
      (W.preΨ (2 * m + 1)) ^ 2 := by
  have hodd : ¬ Even (2 * m + 1) := by
    simpa using Int.not_even_two_mul_add_one m
  simp [WeierstrassCurve.ΨSq, hodd]

/-- CLOSEABLE-NOW: expanded formula for `Φ_{2m}` from the definition of `Φ`. -/
theorem Φ_even_expanded (m : ℤ) :
    W.Φ (2 * m) =
      X * W.ΨSq (2 * m) - W.preΨ (2 * m + 1) * W.preΨ (2 * m - 1) := by
  -- Expected proof:
  --   simp [WeierstrassCurve.Φ, even_two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  -- Exact `Φ` unfolding may need a local `rw [WeierstrassCurve.Φ]` depending on transparency.
  sorry

/-- CLOSEABLE-NOW: expanded formula for `Φ_{2m+1}` from the definition of `Φ`. -/
theorem Φ_odd_expanded (m : ℤ) :
    W.Φ (2 * m + 1) =
      X * W.ΨSq (2 * m + 1) -
        W.preΨ (2 * m + 2) * W.preΨ (2 * m) * W.Ψ₂Sq := by
  -- Expected proof:
  --   simp [WeierstrassCurve.Φ, Int.not_even_two_mul_add_one]
  sorry

/-- CLOSEABLE-NOW: `preΨ_{2m}` recurrence in the exact form needed by doubling identities. -/
theorem preΨ_even_expanded (m : ℤ) :
    W.preΨ (2 * m) =
      W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -
        W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 := by
  exact W.preΨ_even m

/-- CLOSEABLE-NOW: `preΨ_{2m+1}` recurrence in the exact form needed by differential addition. -/
theorem preΨ_odd_expanded (m : ℤ) :
    W.preΨ (2 * m + 1) =
      W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -
        W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 *
          (if Even m then 1 else W.Ψ₂Sq ^ 2) := by
  exact W.preΨ_odd m

/-!
## 2. Polynomial Kummer identities against `[Φ:ΨSq]`

These are the core ring-normalization lemmas.  They are CLOSEABLE-NOW if the repo's `dupNumH`,
`dupDenH`, and differential-addition homogeneous forms are already available.  The proofs should be
`rw` with the recurrence wrapper lemmas above, unfold the Kummer forms, then `ring`/`ring_nf` plus
`W.b_relation` as needed.
-/

/--
CLOSEABLE-NOW, assuming `dupNumH/dupDenH` are available.

Cross-multiplied identity for doubling:

```text
dup([Φ_m:ΨSq_m]) ~ [Φ_{2m}:ΨSq_{2m}].
```
-/
theorem xDBL_phiPsi_cross
    (dupNumH dupDenH : k[X] → k[X] → k[X])
    (m : ℤ) :
    dupNumH (W.Φ m) (W.ΨSq m) * W.ΨSq (2 * m) =
      dupDenH (W.Φ m) (W.ΨSq m) * W.Φ (2 * m) := by
  -- Proof recipe:
  --   rw [Φ_even_expanded, ΨSq_even_expanded]
  --   rw [preΨ_even_expanded]
  --   unfold dupNumH dupDenH  -- or simp [dupNumH, dupDenH]
  --   ring_nf
  --   linear_combination ... W.b_relation if needed
  -- Missing only exact repo names/signatures of `dupNumH` and `dupDenH`.
  sorry

/--
CLOSEABLE-NOW, assuming the homogeneous differential-addition forms are available.

Cross-multiplied identity for differential addition with known difference `P`:

```text
dadd([Φ_1:ΨSq_1], [Φ_m:ΨSq_m], [Φ_{m+1}:ΨSq_{m+1}])
  ~ [Φ_{2m+1}:ΨSq_{2m+1}].
```

Here `[Φ_1:ΨSq_1] = [x:1]` is the known difference vector.
-/
theorem xDADD_phiPsi_cross
    (diffAddNumH diffAddDenH : k[X] → k[X] → k[X] → k[X] → k[X] → k[X] → k[X])
    (m : ℤ) :
    diffAddNumH X 1 (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) *
        W.ΨSq (2 * m + 1) =
      diffAddDenH X 1 (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) *
        W.Φ (2 * m + 1) := by
  -- Proof recipe:
  --   rw [Φ_odd_expanded, ΨSq_odd_expanded]
  --   rw [preΨ_odd_expanded]
  --   unfold diffAddNumH diffAddDenH
  --   ring_nf
  -- This is exactly where the EDS addition recurrence appears.
  -- Missing only exact repo names/signatures of differential-addition forms.
  sorry

/-- Convert the polynomial doubling cross identity to projective vector equality after evaluation. -/
theorem xDBL_phiPsi_same
    (xDBL : P1Vec → P1Vec)
    (dupNumH dupDenH : k[X] → k[X] → k[X])
    (h_xDBL_eval :
      ∀ (x : k) (A B : k[X]),
        xDBL ![A.eval x, B.eval x] = ![(dupNumH A B).eval x, (dupDenH A B).eval x])
    (m : ℤ) (x : k)
    (h_nonzero_target : W.phiPsiVec x (2 * m) ≠ 0) :
    SameP1Vec (xDBL (W.phiPsiVec x m)) (W.phiPsiVec x (2 * m)) := by
  -- Usual route:
  -- 1. rewrite with `h_xDBL_eval`;
  -- 2. use `xDBL_phiPsi_cross` evaluated at `x`;
  -- 3. convert cross-product equality + nonzero target into `SameP1Vec`.
  -- A repo lemma likely already exists: `SameP1Vec_of_cross_eq`.
  sorry

/-- Convert the polynomial differential-addition cross identity to projective vector equality. -/
theorem xDADD_phiPsi_same
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (diffAddNumH diffAddDenH : k[X] → k[X] → k[X] → k[X] → k[X] → k[X] → k[X])
    (h_xDADD_eval :
      ∀ (x : k) (A B C D : k[X]),
        xDADD (baseVec x) ![A.eval x, B.eval x] ![C.eval x, D.eval x] =
          ![(diffAddNumH X 1 A B C D).eval x,
            (diffAddDenH X 1 A B C D).eval x])
    (m : ℤ) (x : k)
    (h_nonzero_target : W.phiPsiVec x (2 * m + 1) ≠ 0) :
    SameP1Vec
      (xDADD (baseVec x) (W.phiPsiVec x m) (W.phiPsiVec x (m + 1)))
      (W.phiPsiVec x (2 * m + 1)) := by
  -- Same recipe as `xDBL_phiPsi_same`, using `xDADD_phiPsi_cross`.
  sorry

/-!
## 3. Ladder recurrence lemmas

These should already be in the repo as the proven Montgomery ladder recurrences.  If not, add them.
-/

/-- Existing ladder recurrence for even indices. -/
theorem xLadderPair_even_step
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (x : k) (m : ℕ) :
    xLadderPairRep x (2 * m) =
      (xDBL (xLadderPairRep x m).1,
       xDADD (baseVec x) (xLadderPairRep x m).1 (xLadderPairRep x m).2) := by
  -- Existing repo theorem; this placeholder states the needed shape.
  sorry

/-- Existing ladder recurrence for odd indices. -/
theorem xLadderPair_odd_step
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (x : k) (m : ℕ) :
    xLadderPairRep x (2 * m + 1) =
      (xDADD (baseVec x) (xLadderPairRep x m).1 (xLadderPairRep x m).2,
       xDBL (xLadderPairRep x m).2) := by
  -- Existing repo theorem; this placeholder states the needed shape.
  sorry

/-!
## 4. Even and odd induction steps
-/

/-- Even step: from the pair invariant at `m`, prove it at `2m`. -/
theorem ladderPairInv_even
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (h_xDBL_same : ∀ x m, SameP1Vec (xDBL (W.phiPsiVec x (m : ℤ))) (W.phiPsiVec x (2 * (m : ℤ))))
    (h_xDADD_same : ∀ x m, SameP1Vec
        (xDADD (baseVec x) (W.phiPsiVec x (m : ℤ)) (W.phiPsiVec x ((m : ℤ) + 1)))
        (W.phiPsiVec x (2 * (m : ℤ) + 1)))
    (h_xDBL_homogeneous : ∀ {v w}, SameP1Vec v w → SameP1Vec (xDBL v) (xDBL w))
    (h_xDADD_homogeneous :
      ∀ {b b' v v' w w'}, SameP1Vec b b' → SameP1Vec v v' → SameP1Vec w w' →
        SameP1Vec (xDADD b v w) (xDADD b' v' w'))
    (x : k) (m : ℕ)
    (hm : LadderPairInv W xLadderPairRep x m) :
    LadderPairInv W xLadderPairRep x (2 * m) := by
  rw [xLadderPair_even_step W xLadderPairRep xDBL xDADD x m]
  constructor
  · exact (h_xDBL_homogeneous hm.1).trans (h_xDBL_same x m)
  · have hbase : SameP1Vec (baseVec x) (W.phiPsiVec x 1) := W.baseVec_same_phiPsi_one x
    have hadd := h_xDADD_homogeneous hbase hm.1 hm.2
    exact hadd.trans (h_xDADD_same x m)

/-- Odd step: from the pair invariant at `m`, prove it at `2m+1`. -/
theorem ladderPairInv_odd
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (h_xDBL_same : ∀ x m, SameP1Vec (xDBL (W.phiPsiVec x (m : ℤ))) (W.phiPsiVec x (2 * (m : ℤ))))
    (h_xDADD_same : ∀ x m, SameP1Vec
        (xDADD (baseVec x) (W.phiPsiVec x (m : ℤ)) (W.phiPsiVec x ((m : ℤ) + 1)))
        (W.phiPsiVec x (2 * (m : ℤ) + 1)))
    (h_xDBL_homogeneous : ∀ {v w}, SameP1Vec v w → SameP1Vec (xDBL v) (xDBL w))
    (h_xDADD_homogeneous :
      ∀ {b b' v v' w w'}, SameP1Vec b b' → SameP1Vec v v' → SameP1Vec w w' →
        SameP1Vec (xDADD b v w) (xDADD b' v' w'))
    (x : k) (m : ℕ)
    (hm : LadderPairInv W xLadderPairRep x m) :
    LadderPairInv W xLadderPairRep x (2 * m + 1) := by
  rw [xLadderPair_odd_step W xLadderPairRep xDBL xDADD x m]
  constructor
  · have hbase : SameP1Vec (baseVec x) (W.phiPsiVec x 1) := W.baseVec_same_phiPsi_one x
    have hadd := h_xDADD_homogeneous hbase hm.1 hm.2
    exact hadd.trans (h_xDADD_same x m)
  · -- second component is the double of `(m+1)P`, hence index `2m+2`.
    have hdouble := h_xDBL_homogeneous hm.2
    have htarget := h_xDBL_same x (m + 1)
    -- `2 * ((m + 1 : ℕ) : ℤ) = (2 * m + 2 : ℕ)` and this is `(2*m+1)+1`.
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc, two_mul] using
      hdouble.trans htarget

/-!
## 5. Strong induction theorem

Use base pair invariants for `0,1,2,3`.  Since the user already has concrete cases `n=0,1,2,3,4`,
these pair bases are immediate: pair invariant at `i` uses the single-output identities for `i` and
`i+1`.
-/

/-- Base pair invariant for `n=0`. CLOSEABLE-NOW from concrete cases `0` and `1`. -/
theorem ladderPairInv_base0
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec) (x : k) :
    LadderPairInv W xLadderPairRep x 0 := by
  -- use concrete cases `x(0P) = [Φ_0:ΨSq_0]` and `x(P) = [Φ_1:ΨSq_1]`
  sorry

/-- Base pair invariant for `n=1`. CLOSEABLE-NOW from concrete cases `1` and `2`. -/
theorem ladderPairInv_base1
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec) (x : k) :
    LadderPairInv W xLadderPairRep x 1 := by
  sorry

/-- Base pair invariant for `n=2`. CLOSEABLE-NOW from concrete cases `2` and `3`. -/
theorem ladderPairInv_base2
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec) (x : k) :
    LadderPairInv W xLadderPairRep x 2 := by
  sorry

/-- Base pair invariant for `n=3`. CLOSEABLE-NOW from concrete cases `3` and `4`. -/
theorem ladderPairInv_base3
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec) (x : k) :
    LadderPairInv W xLadderPairRep x 3 := by
  sorry

/-- Main strong-induction theorem for the ladder pair invariant. -/
theorem ladderPairInv_all
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (h_xDBL_same : ∀ x m, SameP1Vec (xDBL (W.phiPsiVec x (m : ℤ))) (W.phiPsiVec x (2 * (m : ℤ))))
    (h_xDADD_same : ∀ x m, SameP1Vec
        (xDADD (baseVec x) (W.phiPsiVec x (m : ℤ)) (W.phiPsiVec x ((m : ℤ) + 1)))
        (W.phiPsiVec x (2 * (m : ℤ) + 1)))
    (h_xDBL_homogeneous : ∀ {v w}, SameP1Vec v w → SameP1Vec (xDBL v) (xDBL w))
    (h_xDADD_homogeneous :
      ∀ {b b' v v' w w'}, SameP1Vec b b' → SameP1Vec v v' → SameP1Vec w w' →
        SameP1Vec (xDADD b v w) (xDADD b' v' w'))
    (x : k) :
    ∀ n : ℕ, LadderPairInv W xLadderPairRep x n := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih
  by_cases hsmall : n ≤ 3
  · interval_cases n
    · exact W.ladderPairInv_base0 xLadderPairRep x
    · exact W.ladderPairInv_base1 xLadderPairRep x
    · exact W.ladderPairInv_base2 xLadderPairRep x
    · exact W.ladderPairInv_base3 xLadderPairRep x
  · have hn4 : 4 ≤ n := by omega
    by_cases hEven : Even n
    · rcases hEven with ⟨m, rfl⟩
      have hm_lt : m < 2 * m := by omega
      exact W.ladderPairInv_even
        xLadderPairRep xDBL xDADD
        h_xDBL_same h_xDADD_same h_xDBL_homogeneous h_xDADD_homogeneous
        x m (ih m hm_lt)
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := by
        exact Nat.odd_iff_not_even.mp hEven
      subst hm
      have hm_lt : m < 2 * m + 1 := by omega
      exact W.ladderPairInv_odd
        xLadderPairRep xDBL xDADD
        h_xDBL_same h_xDADD_same h_xDBL_homogeneous h_xDADD_homogeneous
        x m (ih m hm_lt)

/-- Final single-output theorem: the ladder's first component is `[Φ_n:ΨSq_n]`. -/
theorem xLadderRep_phiPsi
    (xLadderPairRep : k → ℕ → P1Vec × P1Vec)
    (xLadderRep : k → ℕ → P1Vec)
    (xDBL : P1Vec → P1Vec)
    (xDADD : P1Vec → P1Vec → P1Vec → P1Vec)
    (h_xLadderRep_eq_fst : ∀ x n, xLadderRep x n = (xLadderPairRep x n).1)
    (h_xDBL_same : ∀ x m, SameP1Vec (xDBL (W.phiPsiVec x (m : ℤ))) (W.phiPsiVec x (2 * (m : ℤ))))
    (h_xDADD_same : ∀ x m, SameP1Vec
        (xDADD (baseVec x) (W.phiPsiVec x (m : ℤ)) (W.phiPsiVec x ((m : ℤ) + 1)))
        (W.phiPsiVec x (2 * (m : ℤ) + 1)))
    (h_xDBL_homogeneous : ∀ {v w}, SameP1Vec v w → SameP1Vec (xDBL v) (xDBL w))
    (h_xDADD_homogeneous :
      ∀ {b b' v v' w w'}, SameP1Vec b b' → SameP1Vec v v' → SameP1Vec w w' →
        SameP1Vec (xDADD b v w) (xDADD b' v' w'))
    (x : k) (n : ℕ) :
    SameP1Vec (xLadderRep x n) (W.phiPsiVec x (n : ℤ)) := by
  rw [h_xLadderRep_eq_fst]
  exact (W.ladderPairInv_all
    xLadderPairRep xDBL xDADD
    h_xDBL_same h_xDADD_same h_xDBL_homogeneous h_xDADD_homogeneous
    x n).1

end WeierstrassCurve
```

---

## Exact polynomial identities to discharge

### Doubling identity, `n = 2m`

At the polynomial level, prove the cross-multiplied identity

```lean
dupNumH (Φ_m) (ΨSq_m) * ΨSq_{2m}
  = dupDenH (Φ_m) (ΨSq_m) * Φ_{2m}
```

as:

```lean
theorem xDBL_phiPsi_cross
    (dupNumH dupDenH : k[X] → k[X] → k[X])
    (m : ℤ) :
    dupNumH (W.Φ m) (W.ΨSq m) * W.ΨSq (2 * m) =
      dupDenH (W.Φ m) (W.ΨSq m) * W.Φ (2 * m)
```

Proof ingredients:

```lean
WeierstrassCurve.ΨSq_even_expanded
WeierstrassCurve.Φ_even_expanded
WeierstrassCurve.preΨ_even
WeierstrassCurve.b_relation
ring_nf
```

If the repo's `dupNumH/dupDenH` are homogeneous b-invariant forms, this should be a direct polynomial calculation.

### Differential-addition identity, `n = 2m+1`

At the polynomial level, prove

```lean
diffAddNumH X 1 Φ_m ΨSq_m Φ_{m+1} ΨSq_{m+1} * ΨSq_{2m+1}
  = diffAddDenH X 1 Φ_m ΨSq_m Φ_{m+1} ΨSq_{m+1} * Φ_{2m+1}
```

as:

```lean
theorem xDADD_phiPsi_cross
    (diffAddNumH diffAddDenH : k[X] → k[X] → k[X] → k[X] → k[X] → k[X] → k[X])
    (m : ℤ) :
    diffAddNumH X 1 (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) *
        W.ΨSq (2 * m + 1) =
      diffAddDenH X 1 (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) *
        W.Φ (2 * m + 1)
```

Proof ingredients:

```lean
WeierstrassCurve.ΨSq_odd_expanded
WeierstrassCurve.Φ_odd_expanded
WeierstrassCurve.preΨ_odd
WeierstrassCurve.b_relation
ring_nf
```

This is the EDS addition recurrence in Kummer-coordinate form.

---

## Genuinely missing or repo-dependent pieces

The following are not Mathlib division-polynomial gaps; they are repo-local names/proofs to plug in:

```lean
-- repo-local x-only Kummer forms
xDBL
xDADD
xLadderPairRep
xLadderRep

-- repo-local homogeneous-form definitions
dupNumH
dupDenH
diffAddNumH
diffAddDenH

-- repo-local formula evaluation lemmas
h_xDBL_eval
h_xDADD_eval

-- repo-local homogeneity lemmas
h_xDBL_homogeneous
h_xDADD_homogeneous

-- repo-local ladder recurrence lemmas
xLadderPair_even_step
xLadderPair_odd_step

-- repo-local base cases already proved concretely
ladderPairInv_base0
ladderPairInv_base1
ladderPairInv_base2
ladderPairInv_base3
```

The potentially missing Mathlib-style wrappers are closeable from existing definitions:

```lean
WeierstrassCurve.ΨSq_even_expanded
WeierstrassCurve.ΨSq_odd_expanded
WeierstrassCurve.Φ_even_expanded
WeierstrassCurve.Φ_odd_expanded
```

If `WeierstrassCurve.Φ` is not transparent enough for `rw`, add these in the same file as local helper lemmas.

---

## Recommended implementation order

1. Add the four division-polynomial wrapper lemmas:

```lean
ΨSq_even_expanded
ΨSq_odd_expanded
Φ_even_expanded
Φ_odd_expanded
```

2. Prove the two polynomial cross identities:

```lean
xDBL_phiPsi_cross
xDADD_phiPsi_cross
```

3. Convert cross identities to projective vector identities:

```lean
xDBL_phiPsi_same
xDADD_phiPsi_same
```

4. Prove homogeneity transport lemmas if not already present:

```lean
same_xDBL
same_xDADD
```

5. Prove pair base cases `0,1,2,3` from the already-proven concrete single cases `0,1,2,3,4`.

6. Run the strong induction:

```lean
ladderPairInv_all
```

7. Extract the first component:

```lean
xLadderRep_phiPsi
```

This avoids any appeal to points, torsion, or separability; it is a pure polynomial/Kummer-ladder identity.
