# Q2137 dm1: Minimal Weil-pairing axiom boundary for Miller bilinearity

Date: 2026-06-28.

## Verdict

Yes: bilinearity can and should be axiomatized cleanly for now, but **not** as the raw theorem

```lean
MillerFunction.weilPairing_add_left
```

attached to the current Miller-loop formula.

The clean boundary is an **abstract Weil-pairing package on the `m`-torsion subgroup**, plus one bridge axiom saying that the elliptic-curve Weil pairing supplies such a package.  For the current Mazur torsion-bound scaffold, the truly minimal downstream axiom is even smaller: the existing consequence

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

This single statement already encapsulates the deep inputs: existence of the Weil pairing, bilinearity, alternation, nondegeneracy/perfectness, Galois equivariance, and descent from rational torsion to a rational primitive root of unity.

So the recommendation is:

1. Keep `MillerFunction.lean` as the future implementation skeleton.
2. Do **not** make the current Miller-formula bilinearity the public axiom boundary.
3. Put the temporary axiom at the abstract interface/bridge level.
4. Later replace the bridge axiom by proving that the Miller construction realizes the abstract Weil pairing.

## Why not axiomatize `MillerFunction.weilPairing_add_left` directly?

The current theorem in `MillerFunction.lean` has the shape:

```lean
/-- Bilinearity in the first argument. -/
theorem weilPairing_add_left (m : ℕ) (P₁ P₂ Q S : Point W) :
    weilPairing W m (P₁ + P₂) Q S =
      weilPairing W m P₁ Q S * weilPairing W m P₂ Q S := by
  sorry
```

That is the wrong place to install a durable axiom, for four reasons.

### 1. The theorem is over all points, not just `E[m]`

The Weil pairing is naturally a map

```text
e_m : E[m] × E[m] → μ_m
```

Bilinearity is a property on the torsion subgroup.  The current statement quantifies over arbitrary `Point W` and has no hypotheses

```lean
m • P₁ = 0
m • P₂ = 0
m • Q = 0
```

or subtype such as

```lean
{ P : Point W // m • P = 0 }
```

Axiomatizing the all-points theorem would make the public API stronger than the mathematical theorem you actually need.

### 2. The formula still has an auxiliary point `S`

The mathematical Weil pairing is independent of the auxiliary point after imposing the usual support-avoidance conditions.  But the current formula is

```lean
weilPairing W m P Q S : K
```

and the theorem states the identity for every `S`.  That hides two deep missing theorems:

```text
S is admissible for the four evaluations;
the value is independent of admissible S.
```

Without an admissibility predicate, the raw theorem is not the clean mathematical abstraction.

### 3. `evalAtPoint` is total by skeleton, but evaluation is only partially defined

In the real construction, evaluation of a rational function at a point is valid only when the denominator does not vanish.  The current skeleton uses a total placeholder:

```lean
def evalAtPoint (_f : FunctionField W) (_R : Point W) : K := by
  exact sorry
```

So proving identities about the totalized Miller formula is not the same as proving identities about the actual Weil pairing.

### 4. The standard proof really is divisor theory

The standard proof of additivity in the first argument uses something like:

```text
div(f_{m,P₁+P₂})
  = div(f_{m,P₁}) + div(f_{m,P₂}) + m * div(g_{P₁,P₂})
```

where `g_{P₁,P₂}` is the addition-law correction.  Turning this into the pairing identity then uses principal divisors, evaluation away from support, and Weil reciprocity.  That is a full divisor layer, not a small local proof about the Miller loop.

Therefore the clean temporary axiom should not be a theorem about the current algorithmic formula.  It should be an abstract EC theorem: the canonical Weil pairing exists and has the standard properties.

## Minimal abstract package for bilinearity + the other sorries

The current `WeilPairingInterface.lean` is already pointed in the right direction: it deliberately avoids Miller functions, divisors, and coordinates.  The one correction I would make is that the field currently named `nondegenerate`

```lean
nondegenerate :
  ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

is **not** nondegeneracy.  It is a primitive-pair witness.  It does not imply radical-zero nondegeneracy:

```lean
(∀ Q, e(P,Q) = 1) → P = 0
(∀ P, e(P,Q) = 1) → Q = 0
```

For example, one can have a primitive value on one direct summand and a completely invisible radical summand.  The primitive pair still exists, but left/right nondegeneracy fails.

Use this package shape instead:

```lean
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  /-- The abstract Weil pairing `e_m : T × T → μ_m`. -/
  pairing : T → T → rootsOfUnity m K

  /-- `e_m(0,Q)=1`.  This is derivable from bilinearity in a cancellative
      codomain, but keeping it as a field avoids irrelevant Lean friction. -/
  pairing_zero_left : ∀ Q : T, pairing 0 Q = 1

  /-- `e_m(P,0)=1`. -/
  pairing_zero_right : ∀ P : T, pairing P 0 = 1

  /-- Left additivity. -/
  pairing_add_left : ∀ (P₁ P₂ Q : T),
    pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q

  /-- Right additivity. -/
  pairing_add_right : ∀ (P Q₁ Q₂ : T),
    pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂

  /-- Alternating: `e_m(P,P)=1`. -/
  alternating : ∀ P : T, pairing P P = 1

  /-- Left radical is zero. -/
  nondegenerate_left :
    ∀ P : T, (∀ Q : T, pairing P Q = 1) → P = 0

  /-- Right radical is zero. -/
  nondegenerate_right :
    ∀ Q : T, (∀ P : T, pairing P Q = 1) → Q = 0

  /-- A primitive value exists.  For the actual Weil pairing this comes from
      evaluating on a symplectic basis of `E[m]`.  Keeping it as a field avoids
      having to formalize finite `ZMod m` basis algebra immediately. -/
  primitive_pair :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

Then the previous theorem sorries become field projections:

```lean
namespace WeilPairingData

variable {m : ℕ} {T K : Type*}
variable [AddCommGroup T] [Module (ZMod m) T] [Field K]

/-- Left nondegeneracy: `(∀ Q, e(P,Q)=1) → P=0`. -/
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 :=
  w.nondegenerate_left P h

/-- Right nondegeneracy: `(∀ P, e(P,Q)=1) → Q=0`. -/
theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 :=
  w.nondegenerate_right Q h

/-- The pairing produces a primitive root in the field `K`. -/
theorem exists_primitive_root (w : WeilPairingData m T K) :
    ∃ ζ : K, IsPrimitiveRoot ζ m := by
  obtain ⟨P, Q, hprim⟩ := w.primitive_pair
  exact ⟨rootVal (w.pairing P Q), hprim⟩

end WeilPairingData
```

This captures the Miller-function sorries at the right abstraction level:

| Miller skeleton obligation | Abstract replacement |
| --- | --- |
| `weilPairing_pow_eq_one` | codomain is `rootsOfUnity m K` |
| `weilPairing_add_left` | `pairing_add_left` field |
| `weilPairing_add_right` | `pairing_add_right` field |
| `weilPairing_self` | `alternating` field |
| `weilPairing_nondegenerate` | `nondegenerate_left/right` plus `primitive_pair` |
| `evalAtPoint` | not part of the public axiom boundary |
| Miller divisor identities | later proof that Miller realizes this package |

## The absolute minimal axiom for the current Mazur theorem

For the current final theorem, you do not actually need to expose bilinearity downstream.  `TorsionBound.lean` only needs this implication:

```lean
HasFullRationalTorsion E m → ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then `RootsOfUnity.lean` proves that a primitive rational `m`-th root forces `m ≤ 2`, and the rest of the torsion-bound argument proceeds.

So the smallest possible axiom is exactly:

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

That is a good scaffold axiom.  It is intentionally coarse, but it has the right mathematical boundary: it states the EC consequence needed by Mazur, not a too-strong property of a partially implemented Miller formula.

## Best medium-term design

Use two layers:

### Layer A: abstract pairing interface, no elliptic curves

This is `WeilPairingData` / `AbstractGaloisWeilData`.  It contains the proved pure-algebra theorem:

```lean
theorem primitive_root_in_base
    (D : AbstractGaloisWeilData K₀ L₀ Γ T₀ m) :
    ∃ ζ : K₀, IsPrimitiveRoot ζ m
```

This is the part you already want to keep axiom-free.

### Layer B: one elliptic-curve bridge axiom

Temporarily assert only the construction of the bridge from full rational torsion:

```lean
axiom weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

or keep the same statement under the existing name:

```lean
weil_pairing_primitive_root
```

This bridge axiom means:

```text
The actual elliptic-curve Weil pairing over an algebraic closure exists,
is Galois-equivariant, is alternating/bilinear/perfect, and has a primitive
value on a basis of E[m].
```

The important point is that the axiom is **one bridge**, not separate axioms for every Miller theorem.

## Later replacement path

When you are ready to discharge the bridge, the proof should proceed in this order.

1. Define the actual torsion type over the algebraic closure:

```lean
E_m_torsion := { P : E(ℚbar).Point // m • P = 0 }
```

2. Define the canonical abstract pairing

```lean
e_m : E_m_torsion → E_m_torsion → rootsOfUnity m ℚbar
```

initially either abstractly from EC theory or by the Miller formula with an admissible auxiliary point.

3. Prove the standard package fields:

```lean
pairing_add_left
pairing_add_right
alternating
nondegenerate_left
nondegenerate_right
primitive_pair
```

4. Prove Galois equivariance:

```lean
σ • e_m P Q = e_m (σ • P) (σ • Q)
```

5. Use full rational torsion to show all points of `E[m]` are fixed by Galois.

6. Apply the already-proved pure algebra theorem `primitive_root_in_base`.

7. Replace the bridge axiom with the theorem.

8. Only then connect `MillerFunction.lean` by proving a realization theorem:

```lean
miller_formula_realizes_weil_pairing
```

with hypotheses saying that the auxiliary point avoids all relevant supports.  This theorem should be an implementation theorem, not the primary API used by the Mazur proof.

## Concrete advice for the current files

I would make these changes conceptually, in this order.

### 1. In `WeilPairingInterface.lean`

Change the structure field currently named `nondegenerate` into three fields:

```lean
nondegenerate_left :
  ∀ P : T, (∀ Q : T, pairing P Q = 1) → P = 0

nondegenerate_right :
  ∀ Q : T, (∀ P : T, pairing P Q = 1) → Q = 0

primitive_pair :
  ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

Then close the two current nondegeneracy sorries by projection.

### 2. Keep `primitive_root_in_base` fully proved

That theorem is the valuable pure-algebra core.  It should not know about Miller functions.

### 3. Keep only one EC bridge axiom/sorry

The only remaining deep EC input should be the theorem/axiom currently represented by:

```lean
theorem weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  sorry
```

If you want zero `sorry` in this file while still tracking the dependency, make it an explicit axiom with a name that advertises the mathematical content:

```lean
axiom full_rational_torsion_primitive_root_by_weil_pairing
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Then downstream uses this axiom, and the future proof replaces exactly this declaration.

### 4. Do not import `MillerFunction.lean` into the Mazur bound path yet

`MillerFunction.lean` is useful engineering scaffolding, but importing it into the final Mazur proof before the divisor/evaluation layer exists will force the project to depend on totalized evaluation and over-strong all-point theorems.

## Bottom line

The minimal clean axiom is **not**:

```lean
axiom weilPairing_add_left : ... current Miller formula ...
```

The minimal clean axiom for the current theorem is:

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

The minimal clean reusable interface is:

```lean
WeilPairingData
```

with bilinearity, alternation, radical-zero nondegeneracy, and primitive-pair fields, plus one bridge from the actual elliptic curve to that abstract data.

That bridge is exactly where the divisor theory belongs.  Miller bilinearity should later become evidence for the bridge, not the axiom boundary itself.
