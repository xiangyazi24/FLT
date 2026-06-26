# Q761 (dm1): clean bridge from formal-group tangent to separability of `preΨ'`

## Recommendation

Use **approach (a), but in the narrow first-order/formula-level form**:

> Do not try to build a full elliptic-curve group over `DualNumber K`.  Instead, prove the few first-order identities needed for the contradiction directly from Mathlib’s projective addition formulas over `CommRing`.

This is the most feasible route with the infrastructure you already have:

* Mathlib’s projective formulas `neg`, `addXYZ`, `addX`, `addY`, `addZ`, `negAddY`, `dblXYZ` already work over every `CommRing`, hence over `K[ε]`.
* You already have the formal group law at `O`, and the direct formal multiplication tangent statement `[n]'(0) = n`.
* You already have the dual-number unit lemmas needed to divide by the relevant `Y`/`ψ₂` factors.
* The missing bridge is first-order only.  It does **not** require a global group law on all `K[ε]`-valued points.

Approach (b) is the tempting trap.  The embedding `K → K[ε]` only gives constant dual points.  It does not give Mathlib’s field-level point group law on nonconstant dual points because `K[ε]` is not a field.  You would end up reimplementing the same formula-level operation anyway, but with extra coercion friction.

Approach (c) is mathematically elegant but much larger in Lean.  It requires a robust API for invariant differentials, pullback by multiplication, rational-function denominators, and the exact relation between that denominator and `preΨ'`.  Unless those files are already essentially complete, this is not the shortest path to closing the last sorry.

## The bridge lemma to prove

The clean target is a first-order theorem, not a global group-law theorem over dual numbers.

Use a statement morally like this:

```lean
/-- First-order multiplication bridge at an n-torsion point.

`Pε` is a dual-number deformation of the field point `P`; `δ = (-P) + Pε` is the
corresponding infinitesimal point at `O`, formed using the projective formulas over
`DualNumber K`.  If `n • P = O`, then the local parameter of the formula-level
`n`-fold multiple of `Pε` has tangent `n` times the local parameter tangent of `δ`.
-/
theorem tangent_nsmul_at_torsion_via_formulas
    {K : Type*} [Field K]
    (W : WeierstrassCurve K)
    (n : ℕ) (hn : (n : K) ≠ 0)
    (P : Fin 3 → K)
    (Pε : Fin 3 → DualNumber K)
    (hP : W.Nonsingular P)
    (hPε : (W.map DualNumber.inl).Equation Pε)
    (hred : DualNumber.fst ∘ Pε = P)
    (hnP : formulaNSmul n W P ≈ ![0, 1, 0]) :
    let δ := (W.map DualNumber.inl).addXYZ
      ((W.map DualNumber.inl).neg (DualNumber.inl ∘ P)) Pε
    DualNumber.snd (localParameterAtO δ) ≠ 0 →
      DualNumber.snd (localParameterAtO (formulaNSmul n (W.map DualNumber.inl) Pε))
        = (n : K) * DualNumber.snd (localParameterAtO δ)
```

The exact names should be adjusted to your existing `DualNumber`, `localParameter`, and formula-level `nsmul` definitions.  The important point is the shape: it talks about **formula-level representatives over `DualNumber K`**, and only about the **first-order local parameter**.

Once you have this bridge, the separability proof is short:

1. A double root gives `preΨ'(n) (x + ε) = 0` in `K[ε]`.
2. Use `ψ₂` invertibility to lift `x + ε` to a dual point `Pε` on the curve with reduction `P` and nonzero tangent.
3. The division-polynomial formula gives the formula-level result `[n]Pε = Oε`, or at least local parameter tangent `0`.
4. The bridge gives that same tangent as `(n : K) * tangent(δ)`.
5. Since `(n : K) ≠ 0` and `tangent(δ) ≠ 0`, contradiction.

## How to formalize the bridge without a `K[ε]` group law

### 1. Define a tiny first-order chart API at `O`

Do this over an arbitrary field `K`, but with formulas evaluated in `DualNumber K`.

You need a predicate for a dual representative reducing to `O`:

```lean
def IsInfinitesimalAtO
    (W : WeierstrassCurve K) (Q : Fin 3 → DualNumber K) : Prop :=
  (W.map DualNumber.inl).Equation Q ∧
  DualNumber.fst (Q 0) = 0 ∧
  DualNumber.fst (Q 1) ≠ 0 ∧
  DualNumber.fst (Q 2) = 0
```

Then reuse the local parameter you already have.  The exact projective formula might be your existing
`t = -X*Z/Y` or `t = -X/Y`; keep the one already used in `Atom6LocalParam` / the formal group files.

The key API should be:

```lean
theorem localParameter_addXYZ_firstOrder
    {Q₁ Q₂ : Fin 3 → DualNumber K}
    (h₁ : IsInfinitesimalAtO W Q₁)
    (h₂ : IsInfinitesimalAtO W Q₂) :
    localParameterAtO ((W.map DualNumber.inl).addXYZ Q₁ Q₂)
      = formalGroupLawDual W (localParameterAtO Q₁) (localParameterAtO Q₂)
```

In practice, this should not require new mathematics: it is the dual-number specialization of the formal group law you proved in `FormalGroupW.lean`.  The proof should be by reducing the relevant projective representative to the already-proved formal expansion, then evaluating at dual-number parameters.

### 2. Define formula-level `nsmul` only as much as needed

Do not define a full group structure.  Define a recursive formula-level operation on representatives:

```lean
noncomputable def formulaNSmul
    (n : ℕ) (W : WeierstrassCurve.Projective A) (P : Fin 3 → A) : Fin 3 → A :=
  -- recursion using `Projective.addXYZ` / `dblXYZ`, matching the field-level formulas
```

If such a definition already exists for division-polynomial coordinates, use that instead.  The only theorem you need at `O` is:

```lean
theorem localParameter_formulaNSmul_at_O
    {Q : Fin 3 → DualNumber K}
    (hQ : IsInfinitesimalAtO W Q) :
    localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective Q)
      = formalNsmulDual W n (localParameterAtO Q)
```

Then your proved theorem `[n]'(0)=n` gives immediately:

```lean
theorem tangent_formulaNSmul_at_O
    {Q : Fin 3 → DualNumber K}
    (hQ : IsInfinitesimalAtO W Q) :
    DualNumber.snd (localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective Q))
      = (n : K) * DualNumber.snd (localParameterAtO Q)
```

This is the formal-group tangent theorem specialized to dual numbers.

### 3. Prove only the translation identity needed at first order

For a field point `P` and a dual deformation `Pε` reducing to `P`, define

```lean
let constP : Fin 3 → DualNumber K := DualNumber.inl ∘ P
let δ := (W.map DualNumber.inl).toProjective.addXYZ
  ((W.map DualNumber.inl).toProjective.neg constP) Pε
```

You need two small facts.

First, `δ` is infinitesimal at `O`:

```lean
theorem neg_add_dual_deformation_is_infinitesimal
    (hP : W.Nonsingular P)
    (hPε : (W.map DualNumber.inl).toProjective.Equation Pε)
    (hred : DualNumber.fst ∘ Pε = P) :
    IsInfinitesimalAtO W δ
```

This uses `Projective.map_addXYZ`, `Projective.map_neg`, and the field-level fact `(-P)+P=O` on the reduction.  No group law over `DualNumber K` is needed; only the reduction to `K`, where the group law exists.

Second, the tangent of `δ` is nonzero when the `x`-deformation is nonzero and `ψ₂(P)` is a unit:

```lean
theorem tangent_neg_add_deformation_ne_zero
    (hψ₂ : ψ₂ W P ≠ 0)
    (hxε : DualNumber.snd (Pε 0) ≠ 0) :
    DualNumber.snd (localParameterAtO δ) ≠ 0
```

This is exactly where your `dualNumber_isUnit_of_fst_ne_zero` and `psi2_dual_isUnit` lemmas belong.  It is an implicit-function / tangent-coordinate calculation, not a group-law theorem.

### 4. Replace `[n](P+δ) = [n]P + [n]δ` by a first-order formula lemma

This is the only genuinely new bridge lemma.  State it only in the torsion situation:

```lean
theorem formulaNSmul_dual_deformation_tangent_eq_formalNSmul_delta
    (hnP : nsmulField W n P = O)
    (hδ : IsInfinitesimalAtO W δ) :
    DualNumber.snd
      (localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective Pε))
      = DualNumber.snd
        (localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective δ))
```

Do **not** try to prove this by creating a group over `DualNumber K`.  Prove it by formula reduction:

* map both sides by `DualNumber.fst`; both reduce to `O`, because `n • P = O` over `K`;
* both sides are first-order points at `O`;
* in the local chart at `O`, the projective addition formulas are already identified with the formal group law;
* therefore the first-order term is controlled by `formalNsmul`.

If the full statement is still too hard, specialize further to exactly the representative produced by the division-polynomial formulas.  A narrow theorem with the exact `Pε` used in `preΨ'_deriv_ne_zero_at_nontorsion_root` is acceptable for closing the last sorry.

## Final separability contradiction

The final proof should have the following shape.

```lean
have hPε_on_curve : (W.map DualNumber.inl).Equation Pε := ...
have hPε_reduces : DualNumber.fst ∘ Pε = P := ...
have hδ_inf : IsInfinitesimalAtO W δ :=
  neg_add_dual_deformation_is_infinitesimal W P Pε hP hPε_on_curve hPε_reduces
have hδ_tangent_ne : DualNumber.snd (localParameterAtO δ) ≠ 0 :=
  tangent_neg_add_deformation_ne_zero W P Pε hψ₂ hxε

-- From the assumed double root of `preΨ'`:
have hnPε_is_O :
    DualNumber.snd
      (localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective Pε)) = 0 :=
  divisionPolynomial_dual_vanish_implies_nsmul_tangent_zero ...

-- From the bridge and `[n]'(0)=n`:
have hnPε_tangent :
    DualNumber.snd
      (localParameterAtO (formulaNSmul n (W.map DualNumber.inl).toProjective Pε))
      = (n : K) * DualNumber.snd (localParameterAtO δ) := by
  rw [formulaNSmul_dual_deformation_tangent_eq_formalNSmul_delta ...]
  exact tangent_formulaNSmul_at_O W n hδ_inf

have : (n : K) * DualNumber.snd (localParameterAtO δ) = 0 := by
  simpa [hnPε_tangent] using hnPε_is_O
exact hδ_tangent_ne (mul_eq_zero.mp this |>.resolve_left hn)
```

## Bottom line

The best path is **not** to add a group law on `K[ε]`-points and not to switch to invariant differentials.  The best path is a **first-order formula-level bridge**:

1. use projective formulas over `DualNumber K`;
2. translate the deformation `Pε` to an infinitesimal `δ` at `O` using formulas;
3. use the already-proved formal group tangent theorem at `O`;
4. prove only the torsion-specialized first-order compatibility needed to replace `[n](P+δ) = [n]P + [n]δ`.

This keeps the new work local, avoids a non-field group law, and uses exactly the formal-group and dual-number infrastructure you already proved.
