# Q1139 (dm1): Mazur torsion bound B-line without elliptic Galois representations

## Verdict

For a **0-sorry, 0-custom-axiom** Lean proof of

```lean
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) : m ≤ 2
```

the shortest honest route is **not** pure group theory, not Tate modules, and not class field theory.  It is one of these two:

1. **If a Mazur torsion classification theorem is already available in FLT**, use it.  Then this theorem is almost immediate.
2. **If Mazur is not already formalized**, the shortest honest new formalization is a **minimal Weil-pairing corollary**, not the full elliptic-curve Galois representation:

   ```lean
   HasFullRationalTorsion E m → ∃ ζ : ℚ, IsPrimitiveRoot ζ m
   ```

   Then compose with Mathlib's rational-root-of-unity bound:

   ```lean
   isPrimitiveRoot_rat_order_le_two : IsPrimitiveRoot ζ m → m ≤ 2
   ```

If you forbid both Galois representations and the Weil pairing, then I do **not** see a short no-sorry Mathlib route.  The remaining honest routes, such as Mazur's theorem or the real Lie-group structure of `E(ℝ)`, require major infrastructure not presently exposed as a ready-to-apply Mathlib theorem for Weierstrass curves.

So the practical answer is:

```text
Shortest with existing Mazur theorem: use Mazur classification.
Shortest without Mazur but also without Galois reps: formalize the minimal Weil-pairing corollary.
Shortest without Mazur, Galois reps, and Weil pairing: no short currently available path.
```

## Why `isPrimitiveRoot_rat_order_le_two` is only the final 5 percent

The Mathlib lemma

```lean
isPrimitiveRoot_rat_order_le_two
```

is exactly the last step:

```text
ζ ∈ ℚ primitive m-th root  ⇒  m ≤ 2.
```

But it does not produce `ζ`.  The real missing theorem is:

```text
full rational m-torsion  ⇒  ℚ contains μ_m.
```

That implication is precisely the classical Weil-pairing corollary:

```text
E[m](K) ≅ (ℤ/mℤ)^2  ⇒  μ_m ⊆ K,
```

for `char K ∤ m`.

For `K = ℚ`, this gives a rational primitive `m`th root of unity, and then `isPrimitiveRoot_rat_order_le_two` gives `m ≤ 2`.

## Route 1: direct Weil pairing

### (a) What Mathlib infrastructure exists

Useful pieces already exist or are close to existing in Mathlib/FLT:

* `ZMod m`, products of additive groups, injective additive monoid/group homs;
* `IsPrimitiveRoot`, roots of unity, and the rational bound `isPrimitiveRoot_rat_order_le_two`;
* Weierstrass curves and rational points;
* division-polynomial and torsion-related definitions in the elliptic-curve development, including project-local references such as `WeierstrassCurve.nTorsion`.

What does **not** appear to be available as a ready API is a theorem of the form:

```lean
weilPairing_full_rational_torsion_gives_primitive_root
```

or a complete package:

```text
Weil pairing definition
+ bilinearity
+ alternating/skew-symmetry
+ nondegeneracy
+ rationality on rational torsion points
+ primitive value on a basis
```

### (b) What would need to be built

You do **not** need to expose the full divisor-theory API to the final theorem.  The best target is a narrow project theorem:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
The minimal Weil-pairing corollary needed for the torsion-bound line.

This should be proved from the Weil pairing, but the rest of the FLT project
should depend only on this small statement.
-/
theorem primitiveRoot_of_fullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- Hard local theorem: prove from the Weil pairing.
  -- Do not route through elliptic Galois representations.
  -- Do not expose divisor choices to callers of the torsion-bound theorem.
  sorry

/--
Once the narrow Weil-pairing corollary exists, the desired bound is immediate.
-/
theorem fullRationalTorsion_order_le_two_from_primitiveRoot
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  rcases primitiveRoot_of_fullRationalTorsion
      (E := E) (m := m) hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

end FLT
```

The proof of `primitiveRoot_of_fullRationalTorsion` should use the following mathematical skeleton.

```text
1. Choose P = f(1, 0), Q = f(0, 1) from hfull.
2. Show P and Q have exact order m and generate a subgroup of size m².
3. In characteristic zero, geometric E[m] has size m².
4. Therefore P, Q form a basis of E[m].
5. Nondegeneracy of the Weil pairing gives that e_m(P, Q) is a primitive m-th root.
6. Since P and Q are rational, and the Weil pairing is defined over ℚ,
   e_m(P, Q) is rational.
7. Take ζ = e_m(P, Q).
```

The only genuinely hard ingredients are steps 3, 5, and 6.

Step 6 can be proved without building a full Galois representation.  One can prove directly that the functions/divisors used to define the Weil pairing are defined over `ℚ` and evaluate to `ℚ` on rational torsion data.  That is still Weil-pairing infrastructure, but it is **less** than a mod-`m` Galois representation plus determinant theorem.

### (c) Feasibility estimate

**Feasibility: medium-large, but this is the shortest honest route if Mazur is not already available.**

It is substantial because Lean must know enough divisor/Riemann-Roch/function-field material to define or import the Weil pairing.  But it is still much smaller than formalizing Mazur's theorem or elliptic-curve Galois representations.

Recommended deliverable:

```text
Do not formalize every property of the Weil pairing globally.
Formalize only the corollary:
  full rational m-torsion over ℚ gives a rational primitive m-th root.
```

## Route 2: Tate module / formal group approach

### (a) What Mathlib infrastructure exists

Mathlib has broad algebraic infrastructure: modules, inverse limits in some settings, topology, formal power series, and some formal-group-related algebra.  But the elliptic-curve-specific stack needed here is not a ready theorem:

```text
Tate module of E
Galois action on the Tate module
determinant equals cyclotomic character
comparison with finite E[m]
```

### (b) What would need to be built

A Tate-module proof would require at least:

```text
1. definition of T_l(E) for elliptic curves;
2. Galois action on T_l(E);
3. determinant/cyclotomic compatibility;
4. passage from full rational m-torsion to trivial action on the relevant finite quotient;
5. extraction of μ_m ⊆ ℚ or the m ≤ 2 contradiction.
```

This is essentially the Galois-representation route in a more elaborate form.

### (c) Feasibility estimate

**Feasibility: low as a shortcut.**

It is not a good B-line.  It is longer than a finite-level Weil-pairing proof, and it still needs the same determinant/cyclotomic theorem.

## Route 3: pure group theory / endomorphism-ring extraction

### (a) What Mathlib infrastructure exists

Mathlib has strong group theory:

```text
ZMod
finite abelian groups
group homomorphisms
additive groups
orders of elements
```

This is enough to reason about the abstract injection

```lean
ZMod m × ZMod m →+ E(ℚ).Point
```

as a group-theoretic object.

### (b) What would need to be built

No amount of pure group theory can extract a root of unity from an abstract group injection.  The implication

```text
(Z/mZ)^2 embeds in E(ℚ)  ⇒  μ_m ⊆ ℚ
```

is not a theorem of abelian groups.  It uses the geometry of elliptic curves, specifically the alternating perfect Weil pairing on `E[m]`.

The endomorphism ring also does not solve this.  Even knowing many rational torsion points gives a large finite subgroup of the rational point group, but roots of unity live in the base field.  A bridge from torsion geometry to units of the field is exactly what the Weil pairing supplies.

### (c) Feasibility estimate

**Feasibility: impossible as stated.**

Pure group theory can help with bookkeeping once a pairing exists, but it cannot replace the pairing or a comparable arithmetic-geometric theorem.

## Route 4: completely different approaches avoiding roots of unity

There are two plausible non-root-of-unity strategies, but neither is a short Mathlib route unless the corresponding theorem is already in FLT.

### 4A. Mazur torsion classification

Mazur's theorem says the rational torsion subgroup of an elliptic curve over `ℚ` is one of:

```text
ℤ/nℤ,             n = 1, ..., 10 or 12
ℤ/2ℤ × ℤ/2nℤ,     n = 1, ..., 4.
```

From this classification, no group `(ZMod m)^2` embeds for `m ≥ 3`.  Then `m ≤ 2` follows.

Lean shape:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
Schematic: if FLT already has a Mazur classification/bound theorem, this is the
shortest final route.  The exact statement should use the project's torsion
subgroup API.
-/
theorem fullRationalTorsion_order_le_two_from_Mazur
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  -- Use the FLT/Mazur classification theorem for `E(ℚ)_tors`.
  -- Then rule out an embedded `(ZMod m × ZMod m)` for every `m ≥ 3`
  -- by finite abelian group checking.
  -- This is short only if the classification theorem already exists.
  sorry

end FLT
```

Feasibility:

```text
If Mazur is already formalized: very high, shortest path.
If Mazur must be built now: very low as a shortcut; far larger than Weil pairing.
```

### 4B. Real Lie-group torsion bound

There is a beautiful argument avoiding roots of unity entirely:

```text
E(ℚ)[m] injects into E(ℝ)[m].
E(ℝ) is either a circle or a circle plus one extra component.
Therefore #E(ℝ)[m] is m or at most 2m.
Full rational m-torsion gives m² points.
Thus m² ≤ 2m.
Since m > 0, m ≤ 2.
```

This is mathematically clean and avoids Galois representations and Weil pairing.  But it requires formalizing the real Lie-group/topological classification of `E(ℝ)`:

```text
E(ℝ) ≅ S¹       or       E(ℝ) ≅ S¹ × Z/2Z
```

or at least the weaker theorem:

```lean
#(E(ℝ)[m]) ≤ 2 * m.
```

Mathlib has real topology and group theory, but not a ready elliptic-curve theorem of this exact form for `WeierstrassCurve ℝ`.

Feasibility:

```text
Medium-large mathematically, high risk in Lean.
Probably not shorter than a minimal Weil-pairing corollary.
```

### 4C. Reduction modulo primes plus Hasse bound

One might try:

```text
full rational m-torsion
  ⇒ for every good prime p ∤ m, (Z/mZ)^2 injects into E(𝔽_p)
  ⇒ m² ∣ #E(𝔽_p)
  ⇒ use Hasse bound to contradict.
```

The problem is choosing a good prime `p` uniformly small enough relative to `m` while avoiding the discriminant and primes dividing `m`.  The discriminant can have many small prime factors, so this does not give a clean elementary Lean proof without additional analytic number theory or effective prime-avoidance arguments.

Feasibility:

```text
Low as a general theorem.
Useful for hand computations or fixed curves, not for a uniform formal theorem.
```

## Route-by-route summary

| Route | Existing Mathlib support | What must be built | Feasibility as shortest no-sorry path |
|---|---|---|---|
| Direct Weil pairing | roots of unity, group theory, Weierstrass basics | Weil pairing or at least the corollary `full torsion → primitive root` | Best if Mazur is absent |
| Tate module / formal group | algebra/formal series pieces | Tate module, Galois action, determinant/cyclotomic theorem | Not a shortcut |
| Pure group theory / endomorphism ring | strong group theory | impossible missing arithmetic bridge | Not mathematically sufficient |
| Mazur classification | useful only if already in FLT | full torsion classification if absent | Best if already available; otherwise too large |
| Real Lie group bound | topology/group theory basics | classification or torsion bound for `E(ℝ)` | Elegant but not currently short |
| Reduction mod `p` + Hasse | finite fields/Hasse maybe partly available | uniform good-prime choice and reduction API | Low |

## Recommended theorem factoring

Keep the main theorem small.  Put the hard arithmetic in exactly one lemma.

### If using the Weil-pairing B-line

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
Hard theorem to build without elliptic Galois representations.
Preferred proof: minimal Weil-pairing corollary.
-/
theorem primitiveRoot_of_fullRationalTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  sorry

/-- The desired bound follows immediately from Mathlib's rational-root bound. -/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  rcases primitiveRoot_of_fullRationalTorsion
      (E := E) (m := m) hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

end FLT
```

This is the shortest final proof once the Weil-pairing corollary is available.

### If using a Mazur theorem already present in FLT

The hard lemma should instead be:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

/--
Hard theorem if the project chooses the Mazur-classification route.
This is much shorter only if Mazur's theorem is already formalized.
-/
theorem no_full_rational_torsion_of_three_le_from_Mazur
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  sorry

/-- Final wrapper. -/
theorem fullRationalTorsion_order_le_two_from_no_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  by_contra hnot
  have hm3 : 3 ≤ m := by omega
  exact no_full_rational_torsion_of_three_le_from_Mazur
    (E := E) (m := m) hm3 hfull

end FLT
```

Again, this is only short if the Mazur theorem is already available.

## Final recommendation

For a 0-sorry, 0-custom-axiom proof in the current FLT/Mathlib setting:

```text
1. Do not try pure group theory. It cannot produce roots of unity.
2. Do not use Tate modules/formal groups as a shortcut. They recreate the
   determinant/cyclotomic infrastructure.
3. Use Mazur only if FLT already has a formal Mazur torsion classification.
4. Otherwise, formalize the smallest possible Weil-pairing corollary:
      full rational m-torsion over ℚ gives a rational primitive m-th root.
5. Then finish with isPrimitiveRoot_rat_order_le_two.
```

So the shortest honest path is:

```text
HasFullRationalTorsion E m
  -- minimal Weil-pairing corollary, no Galois representation object
  ⇒ ∃ ζ : ℚ, IsPrimitiveRoot ζ m
  -- existing Mathlib rational root-of-unity bound
  ⇒ m ≤ 2.
```

If the project goal is specifically to avoid **both** Galois representations and Weil-pairing/divisor theory, then the honest answer is that there is no currently short Mathlib proof path.  The next plausible non-Weil path is the real Lie-group torsion bound `#E(ℝ)[m] ≤ 2m`, but that would itself require substantial new elliptic-curve topology infrastructure.
