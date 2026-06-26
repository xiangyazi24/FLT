# Q871 (dm4): global separability of `preΨ' n` from the formal tangent of `[n]`

## Verdict

Mathematically, yes: the clean global proof is exactly the isogeny proof.
If `(n : K) ≠ 0`, then the multiplication map `[n] : E → E` is separable / étale, hence its kernel is reduced, and the division-polynomial zero locus has no multiple roots.
This proof removes the even/odd circularity completely, including the characteristic-`2`, odd-`n` case.

But in Lean, `formalNsmulF_coeff_one` by itself is **not** enough to jump directly to polynomial separability of `preΨ' n`.
It proves the tangent of `[n]` at `O` is multiplication by `(n : K)`.
To use it at a root of `preΨ' n`, you still need two bridge layers:

1. **Move the formal tangent from `O` to an arbitrary torsion point `P`.**
   This is translation-invariance of the differential of a group homomorphism.
2. **Identify the local zero of `[n]^* t_O` at `P` with the local zero of `preΨ' n` in the `x`-coordinate.**
   This is the division-polynomial / local-parameter bridge.

So the right answer is:

```text
formalNsmulF_coeff_one
  + dual-number translation invariance of [n]
  + local division-polynomial unit bridge
  ⇒ rootwise separability of all preΨ' n, simultaneously.
```

This avoids induction, but it does not avoid proving some form of the group law.  It can be done without schemes, at the formula level over `DualNumber K`, but the formula-level proof still has to prove the relevant group-homomorphism identity for `[n]` on dual-number points.

## Why the formal tangent at `O` alone cannot be enough

`formalNsmulF_coeff_one` says that in the formal parameter `t` at `O`,

```text
[n]_F(t) = n t + higher terms.
```

Over dual numbers, if `ε^2 = 0`, this becomes

```text
[n]_F(ε a) = ε ((n : K) * a).
```

Thus the infinitesimal kernel at `O` is trivial when `(n : K) ≠ 0`.

However, a root of `preΨ' n` corresponds to a torsion point `P`, not to `O`.  A general rational self-map of a curve can have nonzero derivative at `O` and still ramify somewhere else.  The only reason `[n]` cannot do that is that `[n]` is a group homomorphism.  Therefore the missing theorem is not purely formal-group-theoretic; it is the translation-invariance of the differential of the group endomorphism `[n]`.

The key identity is

```text
[n](P + Q) = [n]P + [n]Q.
```

If `P` is `n`-torsion, this gives, for `Q` infinitesimal near `O`,

```text
[n](P + Q) = [n]Q.
```

So the local behavior of `[n]` near `P` is the same as the local behavior of `[n]` near `O`, after translating by `P`.

This is the whole global argument in one line.

## Formula-level proof over dual numbers

Yes, this can be proved without scheme theory, but only if you have enough point/formula infrastructure over `DualNumber K`.

Let `Rε(a)` be the infinitesimal point near `O` with formal parameter `ε a`, and let

```text
Pε(a) := P + Rε(a).
```

Assume `n • P = O`.  Then, using the group law over dual numbers,

```text
n • Pε(a)
  = n • (P + Rε(a))
  = n • P + n • Rε(a)
  = O + n • Rε(a)
  = n • Rε(a).
```

By `formalNsmulF_coeff_one`, the formal parameter of `n • Rε(a)` is

```text
ε ((n : K) * a).
```

Therefore, if `(n : K) ≠ 0`, then

```text
n • Pε(a) = O  ⇒  a = 0.
```

This is the dual-number statement that `[n]` is unramified at the torsion point `P`.

A Lean-facing abstract version would look like this, ignoring exact local names:

```lean
/-- Translation-invariance of the tangent of `[n]`, stated only at torsion points. -/
theorem nsmul_dual_no_infinitesimal_kernel_at_torsion
    {K : Type*} [Field K]
    (W : WeierstrassCurve K)
    {n : ℕ} (hn : (n : K) ≠ 0)
    {P : W.Point K} (hP : n • P = 0) :
    ∀ a : K,
      n • W.pointInfinitesimalTranslate P a = W.O → a = 0 := by
  -- 1. Rewrite `pointInfinitesimalTranslate P a` as `P + Rε(a)`.
  -- 2. Use `nsmul_add` over `DualNumber K`:
  --      n • (P + Rε(a)) = n • P + n • Rε(a).
  -- 3. Use `hP`.
  -- 4. Identify `n • Rε(a)` with the formal group `[n]_F` evaluated at `ε a`.
  -- 5. Use `formalNsmulF_coeff_one` and `ε^2 = 0`.
  -- 6. Cancel `(n : K)` using `hn`.
  sorry
```

This theorem is much smaller than a full scheme-theoretic development, but it still requires a real group-law identity over dual numbers.  If the current project only has projective formulas for `[n]` over fields, then this is not yet available for free.

## What exactly must be proved at the formula level

To make the above argument work without schemes, I would isolate the following three lemmas.

### 1. Dual polynomial evaluation

For any polynomial `p : K[X]`,

```text
p(x + ε a) = p(x) + ε a p'(x).
```

Lean skeleton:

```lean
lemma polynomial_eval_dual
    (p : K[X]) (x a : K) :
    evalDual p (x + ε * a) =
      dualOf K (p.eval x) + ε * dualOf K (a * p.derivative.eval x) := by
  -- induction on `p`, or use `aeval` plus `derivative` API
  sorry
```

Consequence:

```text
p(x) = 0 and p'(x) = 0
  ⇒ p(x + ε a) = 0 for every a.
```

This is how a double root becomes an infinitesimal root.

### 2. Translation-invariance of `[n]` over dual numbers

The minimal identity is not all of scheme theory.  It is this restricted group-homomorphism statement:

```text
[n](P + Rε(a)) = [n]P + [n]Rε(a).
```

For a torsion point `P`, this reduces the tangent at `P` to the formal tangent at `O`.

If you want to prove this purely from projective formulas, the target is a polynomial identity between projective triples, after substituting the dual-number coordinates and using `ε^2 = 0`.  That is feasible, but it is exactly the formula-level shadow of the group law.  There is no way around proving some version of this identity: without it, the coefficient of the formal group at `O` gives no information about ramification at other points.

### 3. Local division-polynomial unit bridge

The second bridge is from `[n]` being unramified at `P` to `preΨ' n` having a simple root at `x(P)`.

The right local statement is:

```text
near P,    [n]^* t_O = preΨ'_n(x) · unit
```

or, depending on the exact Mathlib normalization,

```text
near P,    [n]^* t_O = Ψ_n · unit,
```

with `Ψ_n = preΨ'_n(x)` for odd `n`, and

```text
Ψ_n = Ψ_2 · preΨ'_n(x)
```

for even `n`.

The unit factor must be nonzero at `P`.  Once this is known, a double root of `preΨ' n` would force `[n]^* t_O` to have zero differential at `P`, contradicting the dual-number unramifiedness theorem above.

In Lean, I would not try to hide this inside the final theorem.  I would state it explicitly as a local bridge:

```lean
/-- Local bridge between the division polynomial and the pullback of the
formal parameter at `O` by `[n]`.  The exact statement should use the
projective formula names already present in the repo. -/
structure PrePsiLocalBridge
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) (n : ℕ) (P : W.Point K) : Prop where
  torsion_of_root :
    (W.preΨ' n).eval P.x = 0 → n • P = W.O
  x_unramified :
    W.dFy P ≠ 0
  pullback_t_eq_prePsi_mul_unit :
    ∃ u,
      IsUnitAt u P ∧
      LocallyAt P
        (fun Q => W.pullbackFormalParameterByNsmul n Q
               = (W.preΨ' n).eval Q.x * u Q)
```

The actual field names will differ, but this is the needed shape.

## Characteristic `2`

The global argument is especially attractive because it handles the previous characteristic-`2` odd case uniformly.

If `char K = 2` and `n` is odd, then `(n : K) ≠ 0`, so the tangent coefficient of `[n]` is still nonzero.  Thus `[n]` is separable.  There is no even/odd circularity.

The remaining characteristic-`2` issue is not the `[n]` tangent; it is the `x`-coordinate bridge.  The projection to the `x`-line ramifies exactly at the fixed points of negation, i.e. at `2`-torsion points.  For odd `n`, a nonzero `n`-torsion point is not `2`-torsion, so the `x`-coordinate should still be a valid local coordinate at the relevant roots.  In Lean this should appear as a lemma of the form:

```lean
lemma preΨ'_root_not_two_torsion
    {n : ℕ} (hn : (n : K) ≠ 0)
    {P : W.Point K}
    (hroot : (W.preΨ' n).eval P.x = 0) :
    W.dFy P ≠ 0 := by
  -- root gives `n • P = O`; if `dFy P = 0`, then `P` is 2-torsion;
  -- combine `n • P = O` and `2 • P = O` with gcd(n,2)=1 in the relevant case.
  sorry
```

For even `n`, `(n : K) ≠ 0` already implies `char K ≠ 2`, so the usual even division-polynomial factorization is safe.

## Recommended Lean route

I would not try to prove the final theorem directly from `formalNsmulF_coeff_one`.  Instead, split the work into four reusable lemmas.

### Lemma A: formal tangent gives no infinitesimal kernel at `O`

```lean
theorem formal_nsmul_no_infinitesimal_kernel
    {n : ℕ} (hn : (n : K) ≠ 0) :
    ∀ a : K,
      formalNsmulF W n (ε a) = 0 → a = 0 := by
  -- use `formalNsmulF_coeff_one`; all higher terms vanish because `ε^2 = 0`
  sorry
```

### Lemma B: translate Lemma A to every torsion point

```lean
theorem nsmul_no_infinitesimal_kernel_at_torsion
    {n : ℕ} (hn : (n : K) ≠ 0)
    {P : W.Point K} (hP : n • P = W.O) :
    ∀ a : K,
      n • W.pointInfinitesimalTranslate P a = W.O → a = 0 := by
  -- use `[n](P + Q) = [n]P + [n]Q` over dual numbers
  -- then reduce to Lemma A
  sorry
```

### Lemma C: a double root gives a nonzero infinitesimal kernel vector

```lean
theorem infinitesimal_kernel_of_preΨ'_double_root
    {n : ℕ} {x : K}
    (hx : (W.preΨ' n).eval x = 0)
    (hdx : (W.preΨ' n).derivative.eval x = 0) :
    ∃ (P : W.Point K) (a : K),
      a ≠ 0 ∧
      P.x = x ∧
      n • P = W.O ∧
      n • W.pointInfinitesimalTranslate P a = W.O := by
  -- use the local division-polynomial bridge and `p(x + ε a)` formula
  sorry
```

For arbitrary non-algebraically-closed `K`, this lemma may need to be stated after base change to an algebraic closure or to a field extension containing a `y` over the root `x`.  That is normal.  Polynomial separability is geometric, so a base-extension statement is often cleaner than forcing every root to be `K`-rational.

A robust statement is:

```lean
theorem preΨ'_map_rootwise_separable_geometric
    {L : Type*} [Field L] [Algebra K L]
    [IsAlgClosed L]
    {n : ℕ} (hn : (n : L) ≠ 0) :
    ∀ x : L,
      IsRoot ((W.preΨ' n).map (algebraMap K L)) x →
      ¬ IsRoot (derivative ((W.preΨ' n).map (algebraMap K L))) x := by
  sorry
```

Then descend/specialize to the rootwise statement over `K`.

### Lemma D: final simultaneous separability theorem

```lean
theorem preΨ'_rootwise_separable_of_natCast_ne_zero
    {n : ℕ} (hn : (n : K) ≠ 0) :
    ∀ x : K,
      IsRoot (W.preΨ' n) x →
      ¬ IsRoot (derivative (W.preΨ' n)) x := by
  intro x hx hdx
  obtain ⟨P, a, ha, hPx, hPtor, hInf⟩ :=
    W.infinitesimal_kernel_of_preΨ'_double_root hx hdx
  exact ha (W.nsmul_no_infinitesimal_kernel_at_torsion hn hPtor a hInf)
```

This is the desired global proof: no induction on `n`, no even/odd split, no cofactor circularity.

## Practical recommendation

If the repo already has a point API over arbitrary commutative algebras or at least over `DualNumber K`, then the global route is worth pursuing.  The core theorem to build is `nsmul_no_infinitesimal_kernel_at_torsion`, because it packages the entire isogeny argument without schemes.

If the repo only has formal-group computations at `O` and division-polynomial recurrences over `K[X]`, then the global route will require substantial new infrastructure.  In that situation, the induction/recurrence route may still be faster, even though it is mathematically less elegant.

The minimal non-scheme route is therefore:

```text
Do not formalize finite étale group schemes.
Do formalize dual-number points and the restricted identity
    [n](P + Rε) = [n]P + [n]Rε.
Then prove the local unit bridge between [n]^*t_O and preΨ' n.
```

That is the formula-level version of Silverman's Exercise 3.7.  It is global in `n`, handles characteristic `2` correctly when `(n : K) ≠ 0`, and breaks the even/odd circularity for good.
