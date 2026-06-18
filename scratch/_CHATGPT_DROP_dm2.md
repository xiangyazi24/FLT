# ChatGPT Drop File (dm2)

## Goal

For

```text
E  : y² = x³ + x² - x
E' : Y² = X³ - 2X² + 5X,
```

with the 2-isogeny

```text
φ  : E  → E'
φ̂ : E' → E,
```

we want the smallest Lean formalization that connects the concrete descent facts

```text
α(E(Q))     ⊆ {1, -1}
α'(E'(Q))   ⊆ {1, 5}
```

and the known rational torsion list

```text
O,
(0,0),
(1,1),
(1,-1),
(-1,1),
(-1,-1)
```

to the conclusion

```text
E(Q) = these six points.
```

The requested route is “Route B”: no Galois cohomology, but allow explicit exactness statements for the isogenies.

## Executive summary

The facts

```text
α(P) ∈ {1,-1}
```

and the existence of the six torsion points are **not enough by themselves** to prove that all rational points are those six.  The missing ingredient is an exactness/rank bridge.

The minimal bridge can be isolated into two framework lemmas:

1. **Concrete 2-isogeny exact sequence cardinal formula**:

   ```text
   |E(Q)/2E(Q)|
     = |E'(Q)/φ(E(Q))| * |E(Q)/φ̂(E'(Q))| / 2.
   ```

   The divisor `2` is the correction term

   ```text
   |E'[φ̂](Q) / φ(E[2](Q))| = 2,
   ```

   because `E'[φ̂](Q) = {O', (0,0)}` and `φ(E[2](Q)) = {O'}`.

2. **Finitely generated abelian group mod-2 rank formula**:

   ```text
   |E(Q)/2E(Q)| = 2^rank(E) * |E(Q)[2]|.
   ```

   Since `E(Q)[2] = {O,(0,0)}` has size `2`, a bound

   ```text
   |E(Q)/2E(Q)| ≤ 2
   ```

   forces `rank(E)=0`.

Everything else can be concrete and cohomology-free.

## Minimal theorem package

The smallest useful package is this.

### A. Concrete quotient relations

Define three quotient relations directly from the point groups and the explicit isogenies:

```lean
-- P,Q : E(Q)
def SameModDualPhi (P Q : EPoint) : Prop :=
  ∃ R : EpPoint, P - Q = phihat R

-- P,Q : E'(Q)
def SameModPhi (P Q : EpPoint) : Prop :=
  ∃ R : EPoint, P - Q = phi R

-- P,Q : E(Q)
def SameModTwo (P Q : EPoint) : Prop :=
  ∃ R : EPoint, P - Q = 2 • R
```

These are the concrete versions of

```text
E(Q)/φ̂(E'(Q)),
E'(Q)/φ(E(Q)),
E(Q)/2E(Q).
```

No `H¹` occurs.

### B. Descent maps and kernel exactness

For the φ-descent, define the concrete squareclass map

```text
α(P) = x(P) mod squares
```

with the standard special values at `O` and `(0,0)`.  Then prove or assume as the isolated exactness theorem:

```lean
theorem alpha_kernel_exact :
  ∀ P Q : EPoint,
    alpha P = alpha Q ↔ SameModDualPhi P Q := by
  -- explicit algebra using the dual-isogeny formula
  sorry
```

Similarly for the dual descent:

```lean
theorem alpha_dual_kernel_exact :
  ∀ P Q : EpPoint,
    alphaDual P = alphaDual Q ↔ SameModPhi P Q := by
  -- explicit algebra using the φ-isogeny formula
  sorry
```

These two lemmas are the concrete replacement for the cohomological exactness of the connecting maps.

### C. Image bounds from explicit Selmer computations

From the already-proved local obstruction work, state:

```lean
theorem alpha_image_subset :
  ∀ P : EPoint, alpha P = sqOne ∨ alpha P = sqNegOne := by
  -- cover_forces_unit + local obstruction package
  sorry

theorem alpha_dual_image_subset :
  ∀ P : EpPoint, alphaDual P = sqOne ∨ alphaDual P = sqFive := by
  -- dual cover_forces_five_unit + local obstruction package
  sorry
```

Then the quotient cardinal bounds are purely formal:

```lean
theorem card_E_mod_dualPhi_le_two :
    Fintype.card (Quot sameModDualPhiSetoid) ≤ 2 := by
  -- define [P] ↦ alpha P into the two-element set {1,-1}
  -- well-defined by alpha_kernel_exact, injective by the reverse implication
  -- image_subset gives the two-element codomain bound
  sorry

theorem card_Ep_mod_phi_le_two :
    Fintype.card (Quot sameModPhiSetoid) ≤ 2 := by
  -- same proof with alphaDual and {1,5}
  sorry
```

This is the first major “provable from current descent data” layer.

## The exact sequence layer

The explicit isogeny identities are:

```lean
theorem phihat_phi_eq_two :
  ∀ P : EPoint, phihat (phi P) = 2 • P := by
  -- explicit formula check
  sorry

theorem phi_phihat_eq_two :
  ∀ Q : EpPoint, phi (phihat Q) = 2 • Q := by
  -- explicit formula check
  sorry
```

From these, define the two maps on quotients:

```lean
-- E'(Q)/φ(E(Q)) → E(Q)/2E(Q), induced by φ̂
def map_left : Quot sameModPhiSetoid → Quot sameModTwoSetoid :=
  Quot.map phihat sorry

-- E(Q)/2E(Q) → E(Q)/φ̂(E'(Q)), the natural quotient map
def map_right : Quot sameModTwoSetoid → Quot sameModDualPhiSetoid :=
  Quot.map id sorry
```

The concrete exactness statement is:

```lean
theorem explicit_isogeny_exact :
  Exact map_left map_right ∧
  Fintype.card (ker map_left) = 2 := by
  -- Exactness means:
  --   P is zero in E/φ̂(E') iff P = φ̂(Q) modulo 2E.
  -- The kernel of map_left is E'[φ̂](Q) / φ(E[2](Q)).
  -- For this curve: E'[φ̂](Q) = {O',(0,0)} and φ(E[2](Q)) = {O'}.
  sorry
```

For the final rank-zero argument, it is cleaner to expose only the cardinal consequence:

```lean
theorem card_E_mod_two_le_two
    (h1 : Fintype.card (Quot sameModDualPhiSetoid) ≤ 2)
    (h2 : Fintype.card (Quot sameModPhiSetoid) ≤ 2) :
    Fintype.card (Quot sameModTwoSetoid) ≤ 2 := by
  -- Use the exact cardinal formula:
  -- |E/2E| = |E'/φE| * |E/φ̂E'| / 2.
  -- With both factors ≤ 2, get |E/2E| ≤ 2.
  sorry
```

This theorem is the minimal exact-sequence framework.  It does not mention `H¹`.

## The rank/torsion layer

Now isolate the group-theoretic Mordell-Weil input.

First, the rational 2-torsion is exactly:

```text
E(Q)[2] = {O, (0,0)}.
```

State it as:

```lean
theorem E_two_torsion_card :
    Fintype.card ETwoTorsion = 2 := by
  -- y=0 and x(x²+x-1)=0; only rational root is x=0
  sorry
```

Then use the finitely generated abelian group formula:

```lean
theorem rank_zero_of_card_mod_two_le_two
    (hmod2 : Fintype.card (Quot sameModTwoSetoid) ≤ 2) :
    MordellWeilRank EPoint = 0 := by
  -- For a finitely generated abelian group G:
  -- |G/2G| = 2^rank(G) * |G[2]|.
  -- Here |E(Q)[2]| = 2, so |E(Q)/2E(Q)| ≤ 2 forces rank = 0.
  sorry
```

Finally, connect rank zero to the complete torsion list.

The torsion list theorem should be stated as a **complete** torsion classification, not merely existence of six torsion points:

```lean
def torsionSix : Finset EPoint :=
  {O, T00, P11, P1m1, Pneg11, Pneg1m1}

theorem torsionSix_complete :
    ∀ P : EPoint, IsTorsion P ↔ P ∈ torsionSix := by
  -- Use Nagell-Lutz or direct torsion computation already available.
  sorry
```

Then:

```lean
theorem all_points_torsion_of_rank_zero
    (hrank : MordellWeilRank EPoint = 0) :
    ∀ P : EPoint, IsTorsion P := by
  -- finitely generated abelian group: rank zero means every point is torsion
  sorry
```

And the desired point classification follows:

```lean
theorem E_points_are_exactly_torsionSix :
    ∀ P : EPoint, P ∈ torsionSix := by
  have hquot1 : Fintype.card (Quot sameModDualPhiSetoid) ≤ 2 :=
    card_E_mod_dualPhi_le_two
  have hquot2 : Fintype.card (Quot sameModPhiSetoid) ≤ 2 :=
    card_Ep_mod_phi_le_two
  have hmod2 : Fintype.card (Quot sameModTwoSetoid) ≤ 2 :=
    card_E_mod_two_le_two hquot1 hquot2
  have hrank : MordellWeilRank EPoint = 0 :=
    rank_zero_of_card_mod_two_le_two hmod2
  intro P
  exact (torsionSix_complete P).mp (all_points_torsion_of_rank_zero hrank P)
```

This is the minimal Route B endpoint.

## What is genuinely proved by the descent data?

The following is genuinely concrete and does not need Mordell-Weil rank or cohomology:

```lean
theorem descent_bounds_only :
    Fintype.card (EPoint ⧸ φ̂(EpPoint)) ≤ 2 ∧
    Fintype.card (EpPoint ⧸ φ(EPoint)) ≤ 2 := by
  constructor
  · exact card_E_mod_dualPhi_le_two
  · exact card_Ep_mod_phi_le_two
```

This follows from:

```text
image α ⊆ {1,-1},
ker α = image φ̂,
image α' ⊆ {1,5},
ker α' = image φ.
```

The following does **not** follow without framework:

```text
E(Q) is finite,
rank(E)=0,
E(Q) equals the six torsion points.
```

For those, one must add either:

1. the concrete isogeny exact sequence plus the finitely generated abelian group rank formula, or
2. a direct integrality theorem plus integral point classification.

## Minimal “sorry budget”

If the goal is to keep the hard framework isolated, use exactly these `sorry` boundaries:

### Algebraic descent exactness

```lean
theorem alpha_kernel_exact :
  ∀ P Q : EPoint, alpha P = alpha Q ↔ SameModDualPhi P Q := by
  sorry

theorem alpha_dual_kernel_exact :
  ∀ P Q : EpPoint, alphaDual P = alphaDual Q ↔ SameModPhi P Q := by
  sorry
```

These are concrete formula checks.

### Isogeny exact sequence cardinal formula

```lean
theorem card_E_mod_two_le_two
    (h1 : Fintype.card (Quot sameModDualPhiSetoid) ≤ 2)
    (h2 : Fintype.card (Quot sameModPhiSetoid) ≤ 2) :
    Fintype.card (Quot sameModTwoSetoid) ≤ 2 := by
  sorry
```

This is the no-`H¹` exact-sequence theorem.

### Mordell-Weil group theory

```lean
theorem rank_zero_of_card_mod_two_le_two
    (hmod2 : Fintype.card (Quot sameModTwoSetoid) ≤ 2) :
    MordellWeilRank EPoint = 0 := by
  sorry

theorem all_points_torsion_of_rank_zero
    (hrank : MordellWeilRank EPoint = 0) :
    ∀ P : EPoint, IsTorsion P := by
  sorry
```

This is the finitely generated abelian group layer.

### Torsion classification

```lean
theorem torsionSix_complete :
    ∀ P : EPoint, IsTorsion P ↔ P ∈ torsionSix := by
  sorry
```

This is arithmetic but independent of the descent exact sequence.

## Important warning

Do not try to conclude

```text
E(Q) = torsionSix
```

from only

```text
α(P) ∈ {1,-1}
```

and the existence of the six torsion points.  That implication is false as a piece of group theory.  The descent image bound only controls a quotient of `E(Q)`.  To rule out infinite-order points, one needs either:

```text
quotient bounds + exact sequence + finite-generation/rank formula,
```

or

```text
integrality + integral point classification.
```

## Bottom line

The minimal cohomology-free Route B formalization is:

```text
1. α-image bound gives |E/φ̂E'| ≤ 2.
2. α'-image bound gives |E'/φE| ≤ 2.
3. Concrete isogeny exact sequence gives |E/2E| ≤ 2.
4. Since |E[2]| = 2, the finitely generated abelian group formula gives rank(E)=0.
5. Rank zero plus complete torsion classification gives E(Q) = torsionSix.
```

The only non-concrete framework needed is the final finitely generated abelian group fact about `G/2G`.  The isogeny part itself can be formalized directly from the explicit maps `φ`, `φ̂`, their kernels, and the identities

```text
φ̂ ∘ φ = [2],
φ ∘ φ̂ = [2].
```

No formalization of `H¹(Q,E[φ])` is necessary for this route.
