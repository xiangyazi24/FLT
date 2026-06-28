# Q2138 (dm2): Weil-pairing architecture — keep one abstract bridge axiom, make MillerFunction definitions-only

Date: 2026-06-28.

## Verdict

Yes: this is the right architecture.

For the Mazur torsion proof, the clean design is:

```text
Downstream Mazur proof
  depends on
WeilPairingInterface.primitive_root_in_base + one bridge axiom
  not on
concrete Miller-function correctness theorems.
```

So `MillerFunction.lean` should become a **definitions-only / engineering-staging file**:

* it may define `verticalFunction`, `lineFunction`, `gFunction`, `millerLoop`, `MillerState`, and harmless identity simp lemmas;
* it should **not** export theorem claims like bilinearity, `pow_eq_one`, alternating, or nondegeneracy unless those are actually proved from divisor/evaluation theory;
* it should avoid a fake total `evalAtPoint : FunctionField W → Point W → K` if that evaluator is later used to state fake concrete Weil-pairing laws.

Then the only remaining mathematical assumption for Mazur should be the bridge axiom:

```lean
theorem weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  sorry
```

That is exactly the right single seam: it says “the actual elliptic-curve Weil-pairing theorem, plus Galois equivariance, plus full rational torsion, gives a primitive root in the base.”  The rest of the Mazur torsion argument can then be developed without pretending that the Miller-function layer is already formalized.

## Important count correction

On current `ai-scratch`, I count **9 literal `sorry`s**, not 8:

```text
WeilPairingInterface.lean:
  left_nondegenerate       -- line 87
  right_nondegenerate      -- line 92
  weil_interface_bridge    -- line 247

MillerFunction.lean:
  evalAtPoint              -- line 199
  weilPairing_pow_eq_one   -- line 221
  weilPairing_add_left     -- line 227
  weilPairing_add_right    -- line 233
  weilPairing_self         -- line 238
  weilPairing_nondegenerate -- line 245
```

If your intended count is “8”, then one of these has presumably already been solved or not counted locally.  But architecturally, the target should be:

```text
0 concrete MillerFunction sorries
0 fake derived interface sorries
1 real bridge sorry: weil_interface_bridge
```

The two `left_nondegenerate` / `right_nondegenerate` sorries in `WeilPairingInterface` should not remain as proof holes.  With the current field

```lean
nondegenerate : ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

they are not derivable for an arbitrary module `T`.  Either promote them to fields of `WeilPairingData`, or delete them if unused.

## Recommended patch: `WeilPairingInterface.lean`

### Replace the structure fields around nondegeneracy

Change:

```lean
  /-- Nondegeneracy: there exist `P Q : T` such that `e_m(P,Q)` is a
      primitive `m`-th root of unity. -/
  nondegenerate :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

to:

```lean
  /-- Existence of a primitive pairing value.  This is the fact needed for
      `exists_primitive_root`. -/
  exists_primitive_pairing :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
  /-- Left radical is trivial.  This is part of the abstract Weil-pairing API,
      not derivable from `exists_primitive_pairing` for an arbitrary module. -/
  left_nondegenerate :
    ∀ P : T, (∀ Q : T, pairing P Q = 1) → P = 0
  /-- Right radical is trivial. -/
  right_nondegenerate :
    ∀ Q : T, (∀ P : T, pairing P Q = 1) → Q = 0
```

### Replace the two theorem sorries by field projections

Change:

```lean
/-- Left nondegeneracy: `(∀ Q, e(P,Q) = 1) → P = 0`. -/
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 := by
  sorry

/-- Right nondegeneracy: `(∀ P, e(P,Q) = 1) → Q = 0`. -/
theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 := by
  sorry
```

to:

```lean
/-- Left nondegeneracy: `(∀ Q, e(P,Q) = 1) → P = 0`. -/
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 :=
  w.left_nondegenerate P h

/-- Right nondegeneracy: `(∀ P, e(P,Q) = 1) → Q = 0`. -/
theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 :=
  w.right_nondegenerate Q h
```

### Update `exists_primitive_root`

Change:

```lean
  obtain ⟨P, Q, hprim⟩ := w.nondegenerate
```

to:

```lean
  obtain ⟨P, Q, hprim⟩ := w.exists_primitive_pairing
```

This removes the two fake abstract proof holes while preserving the same downstream theorem names.

## Recommended patch: `MillerFunction.lean`

Delete the entire concrete `WeilPairing` properties section.  In other words, remove the block beginning at:

```lean
/-! ## Function-field evaluation and the Weil pairing -/

section WeilPairing

variable (W : Affine K) [IsDomain (CoordinateRing W)]
```

through:

```lean
end WeilPairing
```

This removes:

```lean
def evalAtPoint ... := by
  exact sorry

def weilPairing ... := ...

theorem weilPairing_pow_eq_one ... := by
  sorry

theorem weilPairing_add_left ... := by
  sorry

theorem weilPairing_add_right ... := by
  sorry

theorem weilPairing_self ... := by
  sorry

theorem weilPairing_nondegenerate ... := by
  sorry
```

Do **not** replace these theorem sorries with axioms in `MillerFunction.lean`; that would duplicate the bridge seam and make the axiom boundary less clear.

The definitions-only file should keep everything up to the end of `MillerLoop`, then keep the identity simp lemmas:

```lean
/-! ## Simp lemmas for identity cases -/

section SimpLemmas

variable (W : Affine K)

omit [DecidableEq K] in
@[simp]
theorem verticalFunction_zero : verticalFunction W 0 = 1 :=
  rfl

@[simp]
theorem lineFunction_zero_left (Q : Point W) : lineFunction W 0 Q = 1 := by
  simp [lineFunction]

@[simp]
theorem lineFunction_zero_right (P : Point W) : lineFunction W P 0 = 1 := by
  cases P <;> simp [lineFunction]

end SimpLemmas
```

## Update the module docstring in `MillerFunction.lean`

The current module comment says the file defines the Weil pairing and that all proofs are `sorry`.  After this cleanup, make it explicit that this file is definitions-only:

```lean
/-!
# Miller Function Definitions for the Weil Pairing

This file defines the concrete Miller-function building blocks on an affine
Weierstrass curve `W` over a field `K`:

* `verticalFunction` — the vertical line `X - x_P` in `W.FunctionField`;
* `lineFunction` — the line/tangent/vertical branch through two points;
* `gFunction` — the Miller correction factor;
* `millerLoop` and `millerLoopState` — the double-and-add Miller accumulator.

This file is intentionally **definitions-only**.  It does not claim the divisor
identities, evaluation regularity, bilinearity, root-of-unity property, or
nondegeneracy of the concrete Weil pairing.

For the Mazur torsion proof, the actual Weil-pairing input is isolated in
`WeilPairingInterface.weil_interface_bridge`.  The concrete Miller-function layer
is retained as future implementation scaffolding for eventually discharging that
bridge axiom.
-/
```

Also remove `weilPairing` from the “Main definitions” bullet list unless you keep it behind a separate explicitly partial/regular-evaluation API.

## Why this is better

This architecture has a clean axiom ledger:

```text
Current bad state:
  abstract bridge sorry
  + abstract nondegeneracy proof holes
  + concrete Miller-function theorem holes
  + fake/total evalAtPoint hole

Recommended state:
  one theorem seam only: weil_interface_bridge
```

That is much easier to audit.  It says exactly what remains mathematically unproved:

```text
Construct the actual elliptic-curve Weil pairing and prove its Galois-equivariant
primitive-root consequence for full rational torsion.
```

It also avoids a dangerous intermediate state where `MillerFunction.lean` exports theorem names like

```lean
weilPairing_add_left
weilPairing_nondegenerate
```

that look like real formalized elliptic-curve facts but are actually unsupported.

## What downstream files should import/use

Downstream Mazur files should import/use:

```lean
MazurProof.WeilPairingInterface.weil_interface_bridge
```

or a wrapper theorem derived from it.  They should not depend on:

```lean
MillerFunction.weilPairing_add_left
MillerFunction.weilPairing_pow_eq_one
MillerFunction.weilPairing_nondegenerate
```

because those concrete theorems should not exist until the divisor/evaluation layer exists.

## Final recommendation

Proceed with the cleanup:

1. Make `MillerFunction.lean` definitions-only and remove all concrete Weil-pairing property theorem statements.
2. Promote `left_nondegenerate` and `right_nondegenerate` to fields of `WeilPairingData`, or delete the derived theorem statements if unused.
3. Keep exactly one `sorry` / axiom seam:

```lean
weil_interface_bridge
```

This gives the best current architecture: honest axiom boundary, no fake Miller-function claims, and a clear future path for replacing the bridge with concrete divisor/evaluation formalization.
