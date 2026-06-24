# Q118 (dm1): roots of `preΨ' n` are not roots of `Ψ₂Sq`

## Executive answer

There **is** a clean non-circular general-`n` proof at the polynomial/EDS level.  It is not a per-`n` Sylvester resultant proof.  The right general lemma is an EDS recurrence lemma obtained by setting the EDS parameter

```lean
B := W.Ψ₂Sq.eval x
```

to zero.  In the quotient/evaluation stratum `B = 0`, the reduced division polynomial has an explicit closed form in terms of

```lean
C := W.Ψ₃.eval x
D := W.preΨ₄.eval x.
```

The closed forms are:

```text
preNormEDS' 0 C D (2*m + 1)
  = (-1)^(m*(m-1)/2) * C^(m*(m+1)/2)

preNormEDS' 0 C D (4*m + 2)
  = (2*m + 1) * C^(2*m*(m+1))

preNormEDS' 0 C D (4*(m+1))
  = (m+1) * D * C^(2*m*(m+2)).
```

The even formulas use the two-torsion relation

```text
D^2 + 4*C^3 = 0
```

which is the evaluated polynomial identity

```text
preΨ₄^2 + 4*Ψ₃^3 ≡ 0  mod Ψ₂Sq, b_relation.
```

At a root of `Ψ₂Sq`, the already-proved small resultant certificates give

```text
C ≠ 0     -- Ψ₂Sq and Ψ₃ have no common root
D ≠ 0     -- Ψ₂Sq and preΨ₄ have no common root, needed only in the even case
```

and the scalar factors `(2*m+1 : K)` and `(m+1 : K)` are nonzero exactly because `(n : K) ≠ 0`.  Thus `(W.preΨ' n).eval x ≠ 0` whenever `W.Ψ₂Sq.eval x = 0`, and the target theorem follows by contradiction from `hx : (W.preΨ' n).IsRoot x`.

So the answer to the question is: **yes, it reduces to a parity/divisibility induction on the EDS recurrence**.  Equivalently, in `K[X]/(Ψ₂Sq)` the residue of `preΨ'_n` is an invertible scalar times a power of `Ψ₃`, or an invertible scalar times `preΨ₄` times a power of `Ψ₃`.  This is the general resultant statement in recurrence form.

---

## Minimal lemma chain to add

The cleanest implementation is to add one generic EDS lemma plus three tiny elliptic wrappers.

### 1. Generic EDS closed forms at parameter zero

These lemmas live naturally near `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` or locally in the FLT file.  They are independent of elliptic curves.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]

/-- Odd closed form for the auxiliary normalised EDS at parameter `0`.

This one does not need the relation `D^2 + 4*C^3 = 0`: the odd recurrence at `B = 0`
only ever sees odd-indexed terms. -/
private lemma preNormEDS'_zero_odd
    (C D : K) (m : ℕ) :
    preNormEDS' (0 : K) C D (2*m + 1)
      = (-1 : K) ^ (m * (m - 1) / 2) * C ^ (m * (m + 1) / 2) := by
  -- Prove simultaneously with the two even formulas below, by strong induction on the index.
  -- Base cases: m = 0 gives W₁ = 1; m = 1 gives W₃ = C.
  -- Step: use `preNormEDS'_odd`; after `simp` with the zero parameter, exactly one summand
  -- survives depending on `Even m`.  The exponent and sign arithmetic is `omega`/`ring_nf`.
  -- This is a pure EDS lemma; no curve facts enter.
  sorry

/-- The `4*m+2` closed form at parameter `0`. -/
private lemma preNormEDS'_zero_four_mul_add_two
    (C D : K) (hCD : D ^ 2 + (4 : K) * C ^ 3 = 0) (m : ℕ) :
    preNormEDS' (0 : K) C D (4*m + 2)
      = (2*m + 1 : K) * C ^ (2*m*(m + 1)) := by
  -- Strong induction on the index, using `preNormEDS'_even`.
  -- The only algebraic simplification not handled by the inductive hypotheses is replacing
  -- `D^2` by `-4*C^3`, obtained from `hCD`.
  -- The scalar recurrence collapses to the identity for `2*m+1`.
  sorry

/-- The `4*(m+1)` closed form at parameter `0`. -/
private lemma preNormEDS'_zero_four_mul
    (C D : K) (hCD : D ^ 2 + (4 : K) * C ^ 3 = 0) (m : ℕ) :
    preNormEDS' (0 : K) C D (4*(m + 1))
      = (m + 1 : K) * D * C ^ (2*m*(m + 2)) := by
  -- Strong induction on the index, using `preNormEDS'_even`.
  -- Base m = 0 is W₄ = D.  The recurrence again reduces by `hCD`.
  sorry
```

The three proofs above can also be bundled as one theorem returning all three formulas.  In practice that is less repetition, because the even proofs call the odd formula and each other.

A robust bundled statement is:

```lean
private theorem preNormEDS'_zero_closed_forms
    (C D : K) (hCD : D ^ 2 + (4 : K) * C ^ 3 = 0) :
    (∀ m : ℕ,
      preNormEDS' (0 : K) C D (2*m + 1)
        = (-1 : K) ^ (m * (m - 1) / 2) * C ^ (m * (m + 1) / 2)) ∧
    (∀ m : ℕ,
      preNormEDS' (0 : K) C D (4*m + 2)
        = (2*m + 1 : K) * C ^ (2*m*(m + 1))) ∧
    (∀ m : ℕ,
      preNormEDS' (0 : K) C D (4*(m + 1))
        = (m + 1 : K) * D * C ^ (2*m*(m + 2))) := by
  -- `Nat.strong_induction_on` over the requested index is the least painful proof.
  -- Each recursive call lands at a strictly smaller index because the EDS recurrences use
  -- roughly half-indices.
  -- Use:
  --   preNormEDS'_zero, preNormEDS'_one, preNormEDS'_two,
  --   preNormEDS'_three, preNormEDS'_four,
  --   preNormEDS'_odd, preNormEDS'_even.
  -- The only non-linear field simplification is `D^2 = -4*C^3`, derived by
  --   have hDsq : D^2 = -(4 : K) * C^3 := by linear_combination hCD
  -- and then `ring_nf`.
  sorry
```

This is the only genuinely new induction needed for the general theorem.

### 2. Evaluation of `preΨ'` at a `Ψ₂Sq`-root

The division-polynomial definition is `preNormEDS' (W.Ψ₂Sq^2) W.Ψ₃ W.preΨ₄ n`.  Evaluating at `x` and using `W.Ψ₂Sq.eval x = 0` gives the zero-parameter EDS.

```lean
private lemma eval_preΨ'_of_Ψ₂Sq_eval_zero
    (W : WeierstrassCurve K) (x : K) {n : ℕ}
    (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ' n).eval x =
      preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  -- This is either a direct use of the map/eval lemma for `preNormEDS'`, if available,
  -- or a one-time induction on `n using normEDSRec`.
  -- The intended proof with the existing API is:
  --   simpa [WeierstrassCurve.preΨ', hs]
  --     using congrArg (fun p : K[X] => p.eval x)
  --       (show W.preΨ' n = preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n from rfl)
  -- If `simp` does not look through `preNormEDS'`, prove the generic map lemma:
  --   map_preNormEDS' : map f (preNormEDS' B C D n)
  --     = preNormEDS' (map f B) (map f C) (map f D) n.
  sorry
```

If the existing `map_preΨ'` theorem is in scope, the above becomes:

```lean
private lemma eval_preΨ'_of_Ψ₂Sq_eval_zero'
    (W : WeierstrassCurve K) (x : K) {n : ℕ}
    (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ' n).eval x =
      preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  -- Replace `Polynomial.evalRingHom x` by the exact local name if needed.
  simpa [WeierstrassCurve.preΨ', hs]
    using map_preNormEDS' (Polynomial.evalRingHom x)
      (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

### 3. The small two-torsion base facts

The general induction needs the following wrappers around the small resultant certificates already in the project.

```lean
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- From the already-proved resultant certificate for `Ψ₂Sq` and `Ψ₃`. -/
private lemma Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero
    {x : K} (hs : W.Ψ₂Sq.eval x = 0) :
    W.Ψ₃.eval x ≠ 0 := by
  intro hc
  -- Local certificate is reported as something like
  --   Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero : W.Ψ₃.eval x = 0 → W.Ψ₂Sq.eval x ≠ 0
  exact (Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero (W := W) (x := x) hc) hs

/-- From the already-proved resultant certificate for `Ψ₂Sq` and `preΨ₄`. -/
private lemma preΨ₄_eval_ne_of_Ψ₂Sq_eval_zero
    {x : K} (hs : W.Ψ₂Sq.eval x = 0) :
    W.preΨ₄.eval x ≠ 0 := by
  intro hd
  -- Use the local certificate name for the `Ψ₂Sq`/`preΨ₄` resultant.
  -- Expected shape:
  --   Ψ₂Sq_eval_ne_of_preΨ₄_eval_zero : W.preΨ₄.eval x = 0 → W.Ψ₂Sq.eval x ≠ 0
  exact (Ψ₂Sq_eval_ne_of_preΨ₄_eval_zero (W := W) (x := x) hd) hs

/-- The algebraic relation between `Ψ₃` and `preΨ₄` on the `Ψ₂Sq = 0` stratum. -/
private lemma preΨ₄_eval_sq_add_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_zero
    {x : K} (hs : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 + (4 : K) * (W.Ψ₃.eval x) ^ 3 = 0 := by
  -- Polynomial identity:
  --   preΨ₄^2 + 4*Ψ₃^3 ∈ (Ψ₂Sq, b₂*b₆ - b₄^2 - 4*b₈).
  -- This is a small `ring_nf`/`linear_combination` certificate, independent of `n`.
  -- Suggested implementation:
  --   have hb : W.b₂ * W.b₆ - W.b₄^2 - (4 : K) * W.b₈ = 0 := by
  --     have h := b_relation (W := W); rw [← h]; ring
  --   linear_combination (norm := ring_nf [WeierstrassCurve.Ψ₂Sq,
  --     WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄])
  --     <explicit cofactor in x and the bᵢ> * hs + <explicit cofactor> * hb
  -- In many local setups `ring_nf` after substituting `b_relation` and `hs` is enough;
  -- if not, extract the two small cofactors once from SymPy exactly like the Keystone certs.
  sorry
```

The relation is needed only when `n` is even.  If `n` is odd and the field has characteristic `2`, the proof still works because the odd closed form involves only powers of `C = Ψ₃.eval x`.

---

## Final theorem from the lemma chain

This is the final theorem in the requested form.  It uses no torsion-cardinality lemma, no root-set cardinality, no `preΨ'_separable`, and no geometric `nsmul` facts.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]

private lemma natCast_ne_zero_of_cast_mul_left_ne_zero
    {a b : ℕ} (h : ((a * b : ℕ) : K) ≠ 0) : (b : K) ≠ 0 := by
  intro hb
  apply h
  norm_num [Nat.cast_mul, hb]

private lemma natCast_ne_zero_of_cast_mul_right_ne_zero
    {a b : ℕ} (h : ((a * b : ℕ) : K) ≠ 0) : (a : K) ≠ 0 := by
  intro ha
  apply h
  norm_num [Nat.cast_mul, ha]

/-- A root of the reduced division polynomial cannot be a root of the two-division polynomial. -/
theorem preΨ'_root_Ψ₂Sq_ne
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  classical
  intro hs
  have hC : W.Ψ₃.eval x ≠ 0 :=
    Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero (W := W) hs
  have hEval :
      (W.preΨ' n).eval x =
        preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n :=
    eval_preΨ'_of_Ψ₂Sq_eval_zero (W := W) (x := x) (n := n) hs
  have hx0 :
      preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n = 0 := by
    simpa [hEval] using hx

  rcases n.even_or_odd' with ⟨m, hm | hm⟩
  · -- n = 2*m.
    subst n
    rcases m.even_or_odd' with ⟨r, hr | hr⟩
    · -- n = 4*r.
      subst m
      cases r with
      | zero =>
          -- n = 0, contradicting `(n : K) ≠ 0`.
          simp at hn
      | succ r =>
          -- n = 4*(r+1).
          have hD : W.preΨ₄.eval x ≠ 0 :=
            preΨ₄_eval_ne_of_Ψ₂Sq_eval_zero (W := W) hs
          have hCD :
              (W.preΨ₄.eval x) ^ 2 + (4 : K) * (W.Ψ₃.eval x) ^ 3 = 0 :=
            preΨ₄_eval_sq_add_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_zero (W := W) hs
          have hscalar : ((r + 1 : ℕ) : K) ≠ 0 := by
            intro hsc
            apply hn
            -- Current goal is `((4 * (r + 1) : ℕ) : K) = 0`.
            norm_num [Nat.cast_mul, hsc]
          have hclosed := preNormEDS'_zero_four_mul
            (C := W.Ψ₃.eval x) (D := W.preΨ₄.eval x) hCD r
          have hne :
              preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) (4 * (r + 1)) ≠ 0 := by
            rw [hclosed]
            exact mul_ne_zero (mul_ne_zero hscalar hD)
              (pow_ne_zero _ hC)
          exact hne hx0
    · -- n = 4*r + 2.
      subst m
      have hCD :
          (W.preΨ₄.eval x) ^ 2 + (4 : K) * (W.Ψ₃.eval x) ^ 3 = 0 :=
        preΨ₄_eval_sq_add_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_zero (W := W) hs
      have hscalar : ((2 * r + 1 : ℕ) : K) ≠ 0 := by
        intro hsc
        apply hn
        -- Current goal is `((2 * (2*r + 1) : ℕ) : K) = 0`.
        norm_num [Nat.cast_mul, Nat.cast_add, hsc]
      have hclosed := preNormEDS'_zero_four_mul_add_two
        (C := W.Ψ₃.eval x) (D := W.preΨ₄.eval x) hCD r
      have hne :
          preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) (4*r + 2) ≠ 0 := by
        rw [hclosed]
        exact mul_ne_zero hscalar (pow_ne_zero _ hC)
      exact hne hx0
  · -- n = 2*m + 1.
    subst n
    have hclosed := preNormEDS'_zero_odd
      (C := W.Ψ₃.eval x) (D := W.preΨ₄.eval x) m
    have hne :
        preNormEDS' (0 : K) (W.Ψ₃.eval x) (W.preΨ₄.eval x) (2*m + 1) ≠ 0 := by
      rw [hclosed]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : K) ≠ 0))
        (pow_ne_zero _ hC)
    exact hne hx0

end

end WeierstrassCurve
```

The only nontrivial additions are the generic zero-parameter EDS closed forms and the tiny `preΨ₄^2 + 4*Ψ₃^3` two-torsion identity.  The final theorem itself is just a mod-`4` case split plus nonzero-factor bookkeeping.

---

## Equivalent coprimality statement

The root theorem is the evaluation form of the stronger coprimality lemma:

```lean
theorem preΨ'_isCoprime_Ψ₂Sq_of_natCast_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    IsCoprime (W.preΨ' n) W.Ψ₂Sq := by
  -- To prove this from the root theorem, apply the same root theorem after base-changing
  -- to `AlgebraicClosure K`, then use the standard polynomial fact that two polynomials
  -- over a field are coprime iff they have no common root over an algebraic closure.
  -- The direct theorem requested above does not need this stronger form.
  sorry
```

The quotient formulas imply the resultant shape as well.  For example, modulo `Ψ₂Sq`, every `preΨ'_n` is one of

```text
unit * Ψ₃^e,
unit * preΨ₄ * Ψ₃^e.
```

Since the small certificates already prove `Ψ₂Sq` is coprime to both `Ψ₃` and `preΨ₄` on an elliptic curve, this gives the general resultant/coprimality statement without computing a new Sylvester matrix for each `n`.
