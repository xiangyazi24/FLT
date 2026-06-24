# Q86 (dm2): Planning — `preΨ'_isCoprime_derivative`

Target theorem:

```lean
theorem preΨ'_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

This is a planning note, not a full proof.

## Executive verdict

A direct **strong induction on `n` using only `preΨ'_even` / `preΨ'_odd` and product-rule differentiation is not the route I would choose**.  It is mathematically plausible only if strengthened with substantial extra invariants, but as a Lean implementation it is likely to become more complex than the resultant / nonsingularity route.

The main obstruction is not the recurrence itself; it is the derivative.  Differentiating an EDS recurrence turns a clean algebraic identity into a cancellation-prone Wronskian problem.  To prove squarefreeness, it is not enough to know that the lower division polynomials are squarefree.  One needs a certificate that the derivative of the recursively constructed expression is nonzero at each root of the new expression.  The natural certificate is not the raw product rule; it is the separability of `[n]`, or equivalently a differential/Wronskian identity carrying the scalar `(n : k)`.

The route that looks tractable in Lean is therefore:

1. Continue the **resultant / Bezout / root-exclusion** route for the small base strata (`Ψ₂Sq`, `Ψ₃`, `preΨ₄`) and adjacent exceptional cases.
2. Prove a structural identity for the `x`-coordinate of `[n]`, or a Wronskian-style identity derived from it, where the scalar `(n : k)` appears explicitly.
3. Use the already-proved adjacent-Somos and resultant nonsingularity certificates to discharge the denominators / exceptional strata.
4. Derive `IsCoprime F F.derivative` rootwise or by a Bezout certificate, but avoid expanding the derivative of the full EDS recurrence as the main induction invariant.

## 1. Can strong induction via recurrence prove squarefreeness?

### Naive induction statement

A naive induction would try:

```lean
P n := (n : k) ≠ 0 →
  IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

and then use the recurrence for `preΨ' (2*m)` or `preΨ' (2*m+1)` to express the target in terms of lower `preΨ'` values.

This is not strong enough.

For example, in positive characteristic `p`, from

```lean
((2*m + 1 : ℕ) : k) ≠ 0
```

we do **not** get

```lean
(m : k) ≠ 0
```

or the analogous nonvanishing for `m-1`, `m+1`, `m+2`.  Take `m = p`: then `2*m+1` is nonzero in characteristic `p`, but `(m : k)=0`.  Thus the induction hypotheses for the lower factors may be unavailable exactly when the recurrence uses those lower factors.

This is a serious issue because the differentiated odd recurrence schematically has terms like

```text
(F_{m+2} * F_m^3 - F_{m-1} * F_{m+1}^3)'
```

so it contains `F_m'`, `F_{m+1}'`, etc.  Some of those lower derivatives may not be controlled by the induction hypothesis under the target assumption `((2*m+1 : k) ≠ 0)`.

### Stronger induction that might work

A recurrence induction would need a much stronger package than squarefreeness alone.  Something like:

```lean
structure DivPolyInductionPackage (W : WeierstrassCurve k) (n : ℕ) : Prop where
  squarefree_if_index_unit :
    (n : k) ≠ 0 → IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))
  adjacent_coprime_left :
    IsCoprime (W.preΨ' n) (W.preΨ' (n+1))
  adjacent_coprime_right :
    IsCoprime (W.preΨ' n) (W.preΨ' (n+2))
  no_bad_base_common_roots :
    -- root-exclusion facts involving Ψ₂Sq, Ψ₃, preΨ₄
    True
  wronskian_or_differential_certificate :
    -- a non-expanded derivative identity carrying the scalar (n : k)
    True
```

The essential missing field is the last one.  Adjacent coprimality and Somos identities can prevent the recurrence from degenerating when several nearby terms vanish at the same root.  But they do not by themselves prevent cancellation in the derivative of the recurrence.

### Rootwise picture of the induction step

Let `F_n := W.preΨ' n`.  To prove `IsCoprime F_N F_N.derivative`, over a field one can argue rootwise:

```text
Assume F_N(a) = 0 and F_N'(a) = 0.
Derive contradiction.
```

For an odd recurrence, schematically,

```text
F_{2m+1} = F_{m+2} * F_m^3 - F_{m-1} * F_{m+1}^3
```

or a parity-adjusted variant with `Ψ₂Sq` factors.  At a root `a` of `F_{2m+1}`, the recurrence gives a ratio relation among nearby lower values:

```text
F_{m+2}(a) * F_m(a)^3 = F_{m-1}(a) * F_{m+1}(a)^3.
```

Adjacent-Somos can then be used to rule out many simultaneous vanishing patterns.  The nonsingularity certificates from Q47 handle the base exceptional collisions:

```text
gcd(Ψ₂Sq, Ψ₃) = 1 under Δ ≠ 0,
gcd(Ψ₃, preΨ₄) = 1 under Δ ≠ 0.
```

However, after differentiating, one gets a logarithmic-derivative relation at `a` if all the lower values are nonzero:

```text
F'_{m+2}/F_{m+2} + 3 F'_m/F_m
  = F'_{m-1}/F_{m-1} + 3 F'_{m+1}/F_{m+1}.
```

That relation is not contradicted by lower squarefreeness.  Lower squarefreeness only says `F_i'(a) ≠ 0` when `F_i(a)=0`; it says very little when `F_i(a) ≠ 0`.  Thus the rootwise induction needs a **Wronskian identity** or a **multiplication-by-`n` differential identity**, not merely the recurrence.

### Where `(n : k) ≠ 0` enters

The scalar `(n : k)` should enter through the differential of the multiplication-by-`n` map:

```text
[n]^* ω = n · ω.
```

In `x`-coordinate/division-polynomial language, this is the source of a Wronskian identity whose right-hand side contains `(n : k)` times a product of known nonzero factors.  At a root of `F_n`, that identity is exactly what should imply `F_n'(a) ≠ 0`.

In other words, `(n : k) ≠ 0` is not naturally consumed by the raw EDS recurrence.  It is naturally consumed by the differential identity for `[n]`.

That is the conceptual reason recurrence-only induction is awkward.

## 2. Does product-rule differentiation stay controllable?

Not as the primary proof object.

For the odd branch, the derivative expansion is already of the form:

```text
(F_{m+2} * F_m^3)'
  - (F_{m-1} * F_{m+1}^3)'

= F'_{m+2} * F_m^3
  + 3 * F_{m+2} * F_m^2 * F'_m
  - F'_{m-1} * F_{m+1}^3
  - 3 * F_{m-1} * F_{m+1}^2 * F'_{m+1}.
```

The even branch is worse because the reduced even polynomial has extra `Ψ₂Sq` / parity normalization factors, so the differentiated expression carries additional derivative terms for `Ψ₂Sq` and for the lower factors.

In Lean this causes three problems.

### Problem A: lower derivative hypotheses do not match the target index

As noted above, `char k ∤ N` does not imply `char k ∤ i` for each lower index `i` in the recurrence.  So even if one expands the derivative perfectly, the induction hypotheses do not cover all derivative terms.

### Problem B: squarefreeness of factors does not control derivative of a sum

The recurrence is a difference of products.  Squarefreeness of the individual product factors does not imply squarefreeness of their difference.  A proof must exploit the special elliptic identities, not generic algebra about products.

### Problem C: expression swell and rewriting risk

A proof that repeatedly rewrites

```lean
Polynomial.derivative (W.preΨ'_odd ...)
Polynomial.derivative (W.preΨ'_even ...)
```

will create large goals with many terms.  Even if mathematically possible, it will likely require custom normalization lemmas for every parity case and every `preΨ'` normalization.  This is exactly the kind of proof that becomes brittle under Mathlib changes.

### Controllable alternative

The derivative can be kept controllable if it appears only through a named identity, for example:

```lean
-- schematic, not intended as exact API
theorem preΨ'_wronskian
    (W : WeierstrassCurve k) (n : ℕ) :
    WronskianExpression W n = C (n : k) * NonzeroDenominatorExpression W n := by
  -- proved once from multiplication formulas / Somos identities
```

Then the squarefreeness proof uses this identity at a root of `F_n`, rather than unfolding and differentiating the recurrence inside the induction step.

## 3. Literature orientation

I would not expect the cleanest known argument to be an EDS-only induction on the recurrence.

The standard mathematical proof is geometric:

1. The roots of the relevant division polynomial encode nontrivial `n`-torsion, up to the usual `±P` identification on `x`-coordinates.
2. If `char k ∤ n`, the multiplication morphism `[n] : E → E` is separable because its differential is multiplication by `n` on the invariant differential.
3. Hence the kernel group scheme `E[n]` is reduced/étale.
4. Therefore the corresponding division-polynomial root scheme is reduced away from the known small exceptional strata; equivalently the polynomial is coprime to its formal derivative.

Ward-style EDS recurrences explain the algebraic identities and divisibility properties, but the simple-roots statement is usually proved through division-polynomial/torsion geometry or through a resultant/Wronskian computation, not by a bare recurrence induction.

For this project, the closest recurrence-compatible version is not “EDS implies separable” but rather:

```text
EDS recurrence + adjacent Somos + resultant nonsingularity
  ⇒ denominator/nonzero factors in the [n]-differential identity are coprime to F_n
  ⇒ F_n has no multiple roots when (n:k)≠0.
```

That still uses recurrence/Somos, but only to manage nonvanishing and coprimality of the auxiliary factors, not to inductively expand every derivative.

## 4. Recommended Lean route

### Route A: recurrence-only induction

Status: **high risk / probably not worth it**.

Needed ingredients:

```lean
-- schematic only
lemma preΨ'_strong_induction_step_odd :
    LowerPackage W m → LowerPackage W (m+1) → LowerPackage W (m+2) →
    ((2*m+1 : ℕ) : k) ≠ 0 →
    IsCoprime (W.preΨ' (2*m+1)) (derivative (W.preΨ' (2*m+1))) := by
  -- product rule, recurrence, adjacent Somos, many root cases
  sorry

lemma preΨ'_strong_induction_step_even :
    LowerPackage W (m-2) → LowerPackage W (m-1) → LowerPackage W m →
    LowerPackage W (m+1) → LowerPackage W (m+2) →
    ((2*m : ℕ) : k) ≠ 0 →
    IsCoprime (W.preΨ' (2*m)) (derivative (W.preΨ' (2*m))) := by
  -- worse parity and Ψ₂Sq factors
  sorry
```

Risk points:

* Lower induction hypotheses may be unusable when lower indices vanish in `k`.
* The proof must split many root-vanishing cases.
* The derivative of a recurrence difference has cancellation not controlled by lower squarefreeness.
* Even if it works mathematically, the Lean term is likely brittle and large.

### Route B: resultant / Wronskian route

Status: **tractable and recommended**.

The core shape should be:

```lean
-- Schematic only.  Names and exact expressions should follow the existing API.
lemma preΨ'_multiple_root_forces_bad_factor
    (W : WeierstrassCurve k) [W.IsElliptic] {n : ℕ}
    (hn : (n : k) ≠ 0) {a : k}
    (hroot : (W.preΨ' n).eval a = 0)
    (hderiv : (derivative (W.preΨ' n)).eval a = 0) :
    BadBaseFactor W a = 0 := by
  -- Use a named Wronskian / [n]-differential identity.
  -- The RHS contains `(n : k)` times a product of auxiliary factors.
  -- With hn and hroot/hderiv, force an auxiliary bad factor to vanish.
  sorry

lemma bad_base_factor_impossible
    (W : WeierstrassCurve k) [W.IsElliptic] {a : k} :
    BadBaseFactor W a ≠ 0 := by
  -- Use Q47-style certificates:
  --   Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
  --   Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_of_isElliptic
  --   preΨ₄_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
  -- plus adjacent-Somos root-exclusion as needed.
  sorry

theorem preΨ'_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- Field-polynomial criterion: not coprime gives a common root after passing
  -- to a splitting/algebraic closure, or use an existing `IsCoprime`/roots API.
  -- Apply the previous two lemmas.
  sorry
```

This route is better aligned with the hypothesis `hn`: the scalar `(n : k)` appears exactly once, in the differential identity, rather than being awkwardly distributed among lower recurrence indices.

### Route C: pure universal resultant certificate for each `n`

Status: **conceptually clean but not feasible uniformly**.

One could try to prove

```text
Res_X(preΨ'_n, derivative preΨ'_n) = unit * n^N * Δ^M
```

or a divisibility variant.  This would directly imply squarefreeness from `n ≠ 0` and `Δ ≠ 0`.  But producing and checking explicit certificates uniformly in `n` is not realistic.  This is useful as a sanity check for small `n`, not as the main proof.

## Suggested decomposition for implementation

### Step 0: finalize small nonsingularity certs

Use Q47/Q37 results as hard base facts:

```lean
theorem Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
    [W.IsElliptic] (hc3 : W.Ψ₃.eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0

theorem Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_of_isElliptic
    [W.IsElliptic] (hs : W.Ψ₂Sq.eval x = 0) :
    W.Ψ₃.eval x ≠ 0

theorem preΨ₄_eval_ne_of_Ψ₃_eval_zero_of_isElliptic
    [W.IsElliptic] (hc3 : W.Ψ₃.eval x = 0) :
    (W.preΨ 4).eval x ≠ 0
```

These are the non-circular facts needed when a recurrence or differential identity degenerates into the `Ψ₂Sq`, `Ψ₃`, `preΨ₄` stratum.

### Step 1: prove adjacent root-exclusion lemmas

Use `preΨ_adjacent_somos` to prove root-exclusion patterns of the form:

```lean
-- schematic only
lemma not_three_adjacent_roots
    [W.IsElliptic] {i : ℤ} {a : k} :
    ¬ ((W.preΨ i).eval a = 0 ∧
       (W.preΨ (i+1)).eval a = 0 ∧
       (W.preΨ (i+2)).eval a = 0) := by
  -- adjacent Somos reduces to base nonsingularity certificates
  sorry

lemma adjacent_auxiliary_nonzero_at_preΨ'_root
    [W.IsElliptic] {n : ℕ} {a : k}
    (hroot : (W.preΨ' n).eval a = 0) :
    AuxiliaryProduct W n a ≠ 0 := by
  -- case split by parity and use adjacent Somos + Q47 base certs
  sorry
```

Do not try to include derivatives here.  Keep this layer purely about values and coprimality/nonvanishing.

### Step 2: isolate the derivative into one Wronskian lemma

Prove or import a named identity that is morally the derivative of the multiplication formula.  The exact expression depends on the available Mathlib definitions, but the shape should be:

```lean
-- schematic only
theorem preΨ'_differential_identity
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) :
    DifferentialLHS W n = C (n : k) * DifferentialRHS W n := by
  -- Use multiplication formula / φ_n / ψ_n identities if available.
  -- Otherwise derive once from the already-proved recurrence library.
  sorry
```

The important design choice is that this theorem should be a standalone algebraic identity.  The final separability proof should not unfold the product rule for `preΨ'_even`/`preΨ'_odd` at every induction step.

At a root of `F_n`, this identity should specialize to something like:

```text
constant_or_auxiliary_factor * F_n'(a)
  = (n : k) * nonzero_auxiliary_product.
```

Then `hn` and the nonzero auxiliary-product lemma imply `F_n'(a) ≠ 0`.

### Step 3: convert rootwise non-multiple-root statement to `IsCoprime`

Depending on the existing Mathlib API, use one of two paths.

Path 3A: via roots over an algebraic closure:

```lean
-- schematic only
lemma isCoprime_derivative_of_no_common_root
    {f : k[X]}
    (hroot : ∀ a : AlgebraicClosure k,
      aeval a f = 0 → aeval a (derivative f) ≠ 0) :
    IsCoprime f f.derivative := by
  sorry
```

Path 3B: via gcd / irreducible divisor:

```lean
-- schematic only
lemma isCoprime_derivative_of_no_common_irreducible_factor
    {f : k[X]}
    (h : ∀ p : k[X], Irreducible p → p ∣ f → ¬ p ∣ f.derivative) :
    IsCoprime f f.derivative := by
  sorry
```

The irreducible-factor path may avoid algebraic-closure API friction, but the rootwise path is often closer to the intended geometric argument.

### Step 4: prove the theorem

Final theorem shape:

```lean
variable {k : Type*} [Field k]

namespace WeierstrassCurve

open Polynomial

-- Final target, after the helper identities above.
theorem preΨ'_isCoprime_derivative
    (W : WeierstrassCurve k) [W.IsElliptic] {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- 1. reduce to excluding a common root/factor;
  -- 2. apply `preΨ'_differential_identity` at that root;
  -- 3. use `hn` and auxiliary nonzero facts;
  -- 4. contradiction.
  sorry

end WeierstrassCurve
```

## Risk assessment

### Low risk

* Q47-style resultant certificates for the small base pairs.
* Adjacent-Somos value-level root exclusions, provided the existing theorem is already convenient at integer indices.
* The final wrapper from rootwise simple-root statement to `IsCoprime`, assuming a usable polynomial-root or irreducible-factor API.

### Medium risk

* Normalization mismatches among `preΨ`, `preΨ'`, `Ψ₂Sq`, `Ψ₃`, and `preΨ 4`.
* Parity cases for even reduced polynomials.
* Moving between natural and integer indices in the adjacent-Somos library.

### High risk

* A proof that differentiates `preΨ'_even` / `preΨ'_odd` recursively and tries to close by induction.
* Any induction package that assumes lower-index separability from target-index separability.
* Large `ring_nf` goals generated by repeated unfolding of derivative/product recurrences.

## Bottom line

Strong induction via the recurrence is useful for **value-level coprimality and root-exclusion lemmas**, especially with `preΨ_adjacent_somos`.  It is not the right main engine for the derivative/separability theorem.

The derivative should be handled by one named Wronskian or `[n]^*ω = nω` identity.  The recurrence/Somos machinery should then be used only to prove that the auxiliary factors in that identity do not vanish at roots of `preΨ' n`.  This gives a proof architecture that is much closer to the mathematical reason for the theorem and much more likely to survive in Lean.
