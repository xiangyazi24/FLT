# Q2109 (dm1): Reducing `sorry`s in `WeilPairingInterface.lean`

Date: 2026-06-28.

## Connector status

I attempted to read

```text
FLT/Assumptions/MazurProof/WeilPairingInterface.lean
```

on branch `ai-scratch`, but the GitHub connector currently returns `404 Not Found` for that path.  Repository search through the connector also returned no hits for either

```text
WeilPairingInterface
primitive_root_in_base
left_nondegenerate
```

So the exact local names/fields in the file could not be inspected from the connected repository state available to this session.  The proof below is therefore a targeted patch template for the two pure pairing-theory holes, not a verified edit of the missing source file.

## Classification of the five reported `sorry`s

| Sorry | Status | Reason |
|---|---|---|
| `(1) left_nondegenerate` | should be closable, if it is the weak kernel contradiction for the chosen nontrivial pair | From `e P Q ≠ 1`, a hypothesis `∀ a, e P a = 1` contradicts evaluation at `Q`. |
| `(2) right_nondegenerate` | should be closable, if it is the analogous weak kernel contradiction | From `e P Q ≠ 1`, a hypothesis `∀ a, e a Q = 1` contradicts evaluation at `P`.  If the right-kernel statement is instead about the same vector `P`, use alternating + bilinearity to derive `e Q P = (e P Q)⁻¹`, hence `e Q P ≠ 1`. |
| `(3)` bridge into actual elliptic curve Weil data | genuinely hard | Requires constructing/connecting the real Weil pairing on elliptic-curve torsion. |
| `(4)` bridge/rationality/fixed-torsion data | genuinely hard | Requires proving full rational torsion gives the required Galois-fixed abstract data/basis. |
| `(5)` bridge/nondegeneracy/primitive-value data | genuinely hard | Requires the concrete Weil pairing’s nondegeneracy/primitive value theorem, not just Mathlib algebra. |

Important warning: **global** left nondegeneracy

```lean
∀ P, (∀ Q, e P Q = 1) → P = 0
```

is **not** derivable from the bare existential statement

```lean
∃ P Q, e P Q ≠ 1
```

alone.  Existential nontriviality only proves that the selected nontrivial left/right vectors are not in the corresponding kernels.  To prove full kernel-zero nondegeneracy, the interface needs stronger data, e.g. a `ZMod m` basis together with `IsPrimitiveRoot (e P Q) m`, or an explicit perfectness/nondegeneracy axiom for the pairing.

## Direct proof for the weak selected-vector kernel statements

If the two `sorry`s are currently proving that the selected nontrivial pair has nonzero left and right kernel witnesses, the proofs are extremely short.

Replace the left one by:

```lean
-- Given:
--   hPQ : e P Q ≠ 1
-- Goal shape:
--   ¬ ∀ a, e P a = 1
by
  intro hker
  exact hPQ (hker Q)
```

Replace the right one by:

```lean
-- Given:
--   hPQ : e P Q ≠ 1
-- Goal shape:
--   ¬ ∀ a, e a Q = 1
by
  intro hker
  exact hPQ (hker P)
```

No bilinearity or alternatingness is needed for these exact goal shapes.

## If right-nondegeneracy is stated on the same vector as the left kernel

Sometimes the interface phrases the pair as “`P` is not in the left kernel and `P` is not in the right kernel.”  Then the right-kernel proof needs to turn nontriviality of `e P Q` into nontriviality of `e Q P`.  That is where alternating + bilinearity is used.

The reusable lemma is:

```lean
import Mathlib

private lemma swap_eq_inv_of_alternating
    {T μ : Type*} [AddCommGroup T] [Group μ]
    (e : T → T → μ)
    (map_add_left : ∀ P Q R : T, e (P + Q) R = e P R * e Q R)
    (map_add_right : ∀ P Q R : T, e P (Q + R) = e P Q * e P R)
    (alternating : ∀ P : T, e P P = 1)
    (P Q : T) :
    e Q P = (e P Q)⁻¹ := by
  have hdiag : e (P + Q) (P + Q) = 1 := alternating (P + Q)
  have hprod : e P Q * e Q P = 1 := by
    simpa [map_add_left, map_add_right, alternating P, alternating Q, mul_assoc]
      using hdiag
  calc
    e Q P = (e P Q)⁻¹ * (e P Q * e Q P) := by group
    _ = (e P Q)⁻¹ * 1 := by rw [hprod]
    _ = (e P Q)⁻¹ := by simp

private lemma swap_ne_one_of_ne_one
    {T μ : Type*} [AddCommGroup T] [Group μ]
    (e : T → T → μ)
    (map_add_left : ∀ P Q R : T, e (P + Q) R = e P R * e Q R)
    (map_add_right : ∀ P Q R : T, e P (Q + R) = e P Q * e P R)
    (alternating : ∀ P : T, e P P = 1)
    {P Q : T}
    (hPQ : e P Q ≠ 1) :
    e Q P ≠ 1 := by
  intro hQP
  have hswap := swap_eq_inv_of_alternating e map_add_left map_add_right alternating P Q
  have hPQ_one : e P Q = 1 := by
    calc
      e P Q = ((e P Q)⁻¹)⁻¹ := by simp
      _ = (e Q P)⁻¹ := by rw [← hswap]
      _ = 1 := by simp [hQP]
  exact hPQ hPQ_one
```

Then the “same vector right kernel” proof is:

```lean
-- Given:
--   hPQ : e P Q ≠ 1
--   map_add_left, map_add_right, alternating
-- Goal shape:
--   ¬ ∀ a, e a P = 1
by
  intro hker
  have hQP : e Q P ≠ 1 :=
    swap_ne_one_of_ne_one e map_add_left map_add_right alternating hPQ
  exact hQP (hker Q)
```

This is the proof pattern the file should use if the current second `sorry` is failing because it needs the opposite orientation.

## If the current goals are true global left/right nondegeneracy

If the current sorries are for the stronger goals

```lean
def LeftNondegenerate (e : T → T → μ) : Prop :=
  ∀ P, (∀ Q, e P Q = 1) → P = 0

def RightNondegenerate (e : T → T → μ) : Prop :=
  ∀ Q, (∀ P, e P Q = 1) → Q = 0
```

then the two `sorry`s are **not** closable from only

```lean
∃ P Q, e P Q ≠ 1
```

Counterexample idea: on a rank-two module, an alternating bilinear form may be nontrivial on one quotient but still have a nonzero radical.  For composite `m`, even a determinant pairing scaled by a nonunit can be nontrivial but degenerate.  Full nondegeneracy requires a primitive value on a basis or an explicit perfectness hypothesis.

The right stronger theorem boundary should be one of these:

```lean
-- Option A: assume nondegeneracy directly as abstract Weil-pairing data.
field left_nondegenerate : ∀ P, (∀ Q, e P Q = 1) → P = 0
field right_nondegenerate : ∀ Q, (∀ P, e P Q = 1) → Q = 0
```

or:

```lean
-- Option B: assume a basis and primitive determinant value.
field basisP : T
field basisQ : T
field basis_repr : ∀ R : T, ∃ a b : ZMod m, R = a • basisP + b • basisQ
field primitive_pairing : IsPrimitiveRoot (e basisP basisQ) m
```

Then prove global nondegeneracy by evaluating a kernel element `R = a • P + b • Q` against `Q` and `P`:

```text
e R Q = e P Q ^ a = 1  ⇒  a = 0 in ZMod m
e R P = e Q P ^ b = (e P Q) ^ (-b) = 1  ⇒  b = 0 in ZMod m
```

That is a real module/basis proof, but it needs the basis and primitive-root fields.  It is not a consequence of existential nontriviality alone.

## Recommended patch strategy

1. Open `WeilPairingInterface.lean` locally and inspect the exact goal states for the first two `sorry`s.
2. If the goals are weak selected-vector kernel contradictions, use the direct two-line proofs above.
3. If the second goal has the reversed orientation, add `swap_eq_inv_of_alternating` and `swap_ne_one_of_ne_one`, then use the right-kernel proof above.
4. If the goals are global kernel-zero nondegeneracy, do **not** pretend they follow from `∃ P Q, e P Q ≠ 1`; strengthen the abstract data with either explicit left/right nondegeneracy or basis + primitive pairing data.
5. Leave the bridge sorries as named hard seams.  They are exactly where the concrete elliptic-curve Weil pairing, Galois equivariance, and full-rational-torsion-to-fixed-basis construction must eventually enter.
