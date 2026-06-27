# Q1235 (dm4): `#E(ℝ)[m] ≤ 2m` via complex conjugation

## Executive answer

Yes.  There is a clean algebraic route, and it is better than the eigenvalue argument.

The key point is that the missing fixed-point estimate is a finite `ZMod m` linear-algebra lemma:

```text
Let m > 0 and A ∈ Mat₂(Z/mZ).  If det A = -1 in Z/mZ, then

  #{v ∈ (Z/mZ)^2 : A v = v} ≤ m * gcd(m, 2) ≤ 2m.
```

In particular, for odd `m` the bound is actually `≤ m`, and for even `m` the sharp uniform bound is `≤ 2m`.

This lemma does **not** need topology.  It does not even need `A^2 = 1`, although complex conjugation of course gives `A^2 = 1`.  The determinant condition from the Weil pairing is already enough to prevent `A - I` from being too divisible at every prime.

So the proposed Galois-conjugation route can work:

```text
E(ℝ)[m]
  = E(ℂ)[m]^{conj}
  ≃ ker(A - I : (Z/mZ)^2 → (Z/mZ)^2)
  ≤ m * gcd(m, 2)
  ≤ 2m.
```

This avoids the topological input `E(ℝ)_0 ≃ S^1`.

## Correction to the eigenvalue discussion

The eigenvalue picture is misleading over `Z/mZ` because `Z/mZ` is not generally a field and because the involution is not semisimple at the prime `2`.

Even the diagonal model already shows the issue.  For

```text
A = diag(1, -1) on (Z/mZ)^2,
```

the fixed vectors satisfy

```text
(x, y) = (x, -y),  i.e.  2y = 0.
```

Therefore

```text
#Fix(A) = m * gcd(m, 2).
```

So the fixed subgroup is `m`, not `2m`, only when `m` is odd.  When `m` is even it is `2m`.  This is exactly why the final target bound should be `2m`, and it is sharp.

The determinant formula

```text
#ker(A - I) = |det(A - I)|^{-1} * m^2
```

is not valid over `Z/mZ`: `det(A - I)` can be a zero divisor or zero, and there is no such division formula in general.  The right replacement is a local divisibility/Smith-normal-form argument.

## The finite algebra lemma

Here is the clean statement to isolate.

```text
Lemma fixed_card_le_mul_gcd_two.
Let m > 0 and A ∈ Mat₂(Z/mZ).  If det A = -1, then

  #{v : (Z/mZ)^2 | A v = v} ≤ m * gcd(m, 2).
```

The desired `≤ 2m` is then immediate.

### Proof by prime-power localization

Let

```text
B = A - I.
```

By the Chinese remainder theorem, it is enough to prove the corresponding estimate after reducing modulo each prime power `q = p^e` dividing `m`; the fixed subgroup modulo `m` is the product of the fixed subgroups modulo the prime-power factors.

So work over

```text
R = Z/qZ,   q = p^e.
```

We use one elementary observation.

### Unit-entry observation

If some entry of `B` is a unit in `R`, then

```text
#ker(B : R^2 → R^2) ≤ q.
```

Indeed, suppose for example the first-row, first-column entry is a unit.  Then the first row equation

```text
b₁₁ x + b₁₂ y = 0
```

determines `x` uniquely once `y` is chosen.  There are `q` choices for `y`, and the second row equation can only cut this set down.

### Odd prime-power case

Assume `p` is odd.  If every entry of `B = A - I` were divisible by `p`, then

```text
A ≡ I mod p,
```

hence

```text
det A ≡ 1 mod p.
```

But `det A = -1`, and for odd `p` we have `-1 ≠ 1 mod p`.  Contradiction.

Thus some entry of `B` is a unit modulo `p^e`, and the unit-entry observation gives

```text
#ker(A - I) ≤ p^e.
```

So every odd prime-power factor contributes at most its own size.

### Two-power case

Now take `q = 2^e`.

If `e = 1`, the whole ambient module has size

```text
#(Z/2Z)^2 = 4 = 2q,
```

so the desired local bound is trivial.

Assume `e ≥ 2`.  If some entry of `B` is a unit, the unit-entry observation gives

```text
#ker(B) ≤ q ≤ 2q.
```

Otherwise every entry of `B` is even, so

```text
A ≡ I mod 2.
```

They cannot all be divisible by `4`, because then

```text
A ≡ I mod 4,
```

which would imply

```text
det A ≡ 1 mod 4,
```

contradicting

```text
det A = -1 ≡ 3 mod 4.
```

So at least one entry of `B` is exactly divisible by `2`.  In a row containing such an entry, after possibly swapping coordinates, the row equation has the form

```text
2 * (u x + c y) = 0
```

with `u` a unit in `Z/2^eZ`.

In `Z/2^eZ`, the equation

```text
2t = 0
```

has exactly two solutions for `t`, namely `0` and `2^(e-1)`.  Therefore, for each chosen `y`, the expression `u x + c y` has at most two possible values; since `u` is a unit, each such value determines a unique `x`.

Hence

```text
#ker(B) ≤ 2q.
```

### Multiplying the local estimates

Multiplying over all prime powers gives

```text
#ker(A - I) ≤ m
```

if `m` is odd, and

```text
#ker(A - I) ≤ 2m
```

if `m` is even.  Equivalently,

```text
#ker(A - I) ≤ m * gcd(m, 2) ≤ 2m.
```

This proves the finite algebra lemma.

## Why `A^2 = 1` is still useful, but not necessary

For complex conjugation we also have

```text
A^2 = I.
```

This gives a more conceptual odd-prime proof: when `2` is invertible, the idempotents

```text
(1 + A) / 2,   (1 - A) / 2
```

split the module into `+1` and `-1` eigenspaces.  Since `det A = -1`, those eigenspaces have ranks `1` and `1`, so the fixed subgroup has size exactly `p^e` locally at odd primes.

But at the prime `2`, the idempotent splitting is unavailable.  The divisibility argument above handles the `2`-primary obstruction and gives the extra factor `2`.

For Lean, I would use the divisibility proof rather than an eigenvalue/idempotent proof, because it is uniform and avoids semisimplicity issues.

## Applying the lemma to `E(ℝ)[m]`

The algebraic route needs three elliptic-curve inputs.

### 1. Torsion over `ℂ` as a free `ZMod m` module of rank two

For `m > 0`, over characteristic zero,

```text
E(ℂ)[m] ≃ (Z/mZ)^2
```

as a `ZMod m` module.

If the current FLT bridge only says

```text
#E(ℂ)[m] = m^2,
```

then it is too weak for this argument.  The matrix/determinant route needs a basis, or at least a `ZMod m`-linear equivalence with `(ZMod m)^2`.  The cardinality theorem should be a corollary of this stronger structure theorem, not the only available statement.

### 2. Real points are fixed complex points

Complex conjugation acts on `E(ℂ)` because the curve is defined over `ℝ`.  Algebraically,

```text
E(ℝ)[m] = E(ℂ)[m]^{conj}.
```

This is descent for points: a complex point has real coordinates exactly when it is fixed by conjugation.  No connected-component or circle argument is involved.

### 3. The conjugation matrix has determinant `-1`

Choose a `ZMod m` basis `P, Q` of `E(ℂ)[m]`.  Let `A` be the matrix of complex conjugation in this basis.

The Weil pairing gives

```text
e_m(aP + bQ, cP + dQ) = e_m(P, Q)^(ad - bc).
```

Thus the action of a matrix on the Weil pairing is by exponentiating with its determinant.

On the other hand, complex conjugation acts on `μ_m` by inversion:

```text
ζ ↦ ζ⁻¹.
```

Therefore

```text
e_m(conj P, conj Q)
  = conj(e_m(P, Q))
  = e_m(P, Q)⁻¹.
```

Since the Weil pairing is perfect and `e_m(P,Q)` is primitive, this implies

```text
det A = -1 in Z/mZ.
```

Then the finite algebra lemma gives

```text
#E(ℝ)[m]
  = #Fix(A)
  ≤ m * gcd(m, 2)
  ≤ 2m.
```

## Lean target: isolate the matrix lemma first

I would first prove a completely elliptic-curve-free theorem about `ZMod m` matrices.  The exact names below are schematic, but the statement is the important part.

```lean
import Mathlib

namespace FLT
namespace ConjugationFixedCount

open Matrix

noncomputable section

/-- Fixed vectors of a `2 × 2` matrix over `ZMod m`. -/
def FixedVec (m : ℕ) [NeZero m]
    (A : Matrix (Fin 2) (Fin 2) (ZMod m)) : Type :=
  {v : Fin 2 → ZMod m // A.mulVec v = v}

instance (m : ℕ) [NeZero m]
    (A : Matrix (Fin 2) (Fin 2) (ZMod m)) :
    Fintype (FixedVec m A) := by
  dsimp [FixedVec]
  infer_instance

/--
Pure finite-linear-algebra lemma.

Recommended proof strategy:
* use CRT to reduce to `ZMod (p^e)`;
* for odd `p`, `A - 1` has a unit entry, otherwise `det A ≡ 1 mod p`;
* for `2^e`, either `A - 1` has a unit entry, or it is divisible by `2` but not by `4`;
* a unit row equation gives at most `q` solutions;
* a `2 * unit` row equation over `ZMod (2^e)` gives at most `2q` solutions.
-/
theorem card_fixedVec_le_mul_gcd_two
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin 2) (Fin 2) (ZMod m))
    (hdet : A.det = (-1 : ZMod m)) :
    Fintype.card (FixedVec m A) ≤ m * Nat.gcd m 2 := by
  -- This is the standalone algebra lemma to prove.
  -- It should not mention elliptic curves, real points, topology, or the Weil pairing.
  sorry

/-- The weaker form needed downstream. -/
theorem card_fixedVec_le_two_mul
    {m : ℕ} [NeZero m]
    (A : Matrix (Fin 2) (Fin 2) (ZMod m))
    (hdet : A.det = (-1 : ZMod m)) :
    Fintype.card (FixedVec m A) ≤ 2 * m := by
  have h := card_fixedVec_le_mul_gcd_two (m := m) A hdet
  have hg : Nat.gcd m 2 ≤ 2 := Nat.gcd_le_right m (by decide : 0 < 2)
  nlinarith [h, Nat.mul_le_mul_left m hg]

end
end ConjugationFixedCount
end FLT
```

The local row-equation lemmas can be proved separately.  They are often easier than invoking full Smith normal form.

```lean
import Mathlib

namespace FLT
namespace ConjugationFixedCount

noncomputable section

/--
Schematic local counting lemma: over `ZMod q`, if one row of a linear equation
has a unit coefficient, then that row cuts `R^2` down to at most `q` points.
-/
theorem card_kernel_le_of_unit_entry
    {q : ℕ} [NeZero q]
    (B : Matrix (Fin 2) (Fin 2) (ZMod q))
    (i j : Fin 2)
    (hunit : IsUnit (B i j)) :
    Fintype.card {v : Fin 2 → ZMod q // B.mulVec v = 0} ≤ q := by
  -- Choose the other coordinate freely.
  -- The `i`-th row equation determines coordinate `j` uniquely
  -- because `B i j` is a unit.
  sorry

/--
Schematic two-primary row-counting lemma: over `ZMod (2^e)`, if one row is
`2` times a row with a unit coefficient, then that row leaves at most
`2 * 2^e` possibilities.
-/
theorem card_kernel_le_two_mul_of_two_times_unit_entry
    {e : ℕ} (he : 1 ≤ e)
    (B C : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ e)))
    (hB : B = 2 • C)
    (i j : Fin 2)
    (hunit : IsUnit (C i j)) :
    Fintype.card {v : Fin 2 → ZMod (2 ^ e) // B.mulVec v = 0} ≤ 2 * 2 ^ e := by
  -- Use that `{t : ZMod (2^e) // 2 * t = 0}` has cardinal `2`.
  -- For each choice of the other coordinate and each of the two possible
  -- values of the row expression, the unit coefficient determines coordinate `j`.
  sorry

end
end ConjugationFixedCount
end FLT
```

## Project-level theorem shape

After the matrix lemma is available, the elliptic-curve theorem should be a short composition of bridges.

The following is intentionally schematic because it depends on the actual FLT names for elliptic curves, torsion points, base change, and the Weil pairing.

```lean
import Mathlib

namespace FLT
namespace RealTorsionBound

open Matrix

noncomputable section

/-- Placeholder for the project's type of `m`-torsion complex points. -/
axiom ECm (E : Type) (m : ℕ) : Type

/-- Placeholder for the project's type of `m`-torsion real points. -/
axiom ERm (E : Type) (m : ℕ) : Type

/-- Algebraic torsion structure over `ℂ`: stronger than cardinality `m^2`. -/
axiom complex_torsion_zmod_rank_two
    (E : Type) (m : ℕ) [NeZero m] :
    ECm E m ≃ (Fin 2 → ZMod m)

/-- Real `m`-torsion equals fixed complex `m`-torsion under conjugation. -/
axiom real_torsion_equiv_conj_fixed
    (E : Type) (m : ℕ) [NeZero m] :
    ERm E m ≃
      {v : ECm E m // True}

/-- Matrix of complex conjugation after choosing a `ZMod m` basis of `E(ℂ)[m]`. -/
axiom conjMatrix
    (E : Type) (m : ℕ) [NeZero m] :
    Matrix (Fin 2) (Fin 2) (ZMod m)

/-- Weil-pairing anti-symplecticity: complex conjugation has determinant `-1`. -/
axiom conjMatrix_det
    (E : Type) (m : ℕ) [NeZero m] :
    (conjMatrix E m).det = (-1 : ZMod m)

/-- Final desired shape, after replacing placeholders by FLT's actual definitions. -/
theorem real_m_torsion_card_le_two_mul
    (E : Type) (m : ℕ) [NeZero m] :
    Fintype.card (ERm E m) ≤ 2 * m := by
  -- 1. identify `ERm E m` with fixed vectors of `conjMatrix E m`;
  -- 2. apply `ConjugationFixedCount.card_fixedVec_le_two_mul`;
  -- 3. use `conjMatrix_det` from the Weil pairing.
  -- The details are definitional/API wiring once the three bridges above exist.
  sorry

end
end RealTorsionBound
end FLT
```

The important Lean architecture is:

```text
finite matrix lemma
  + complex torsion free rank two over ZMod m
  + real points = conjugation fixed points
  + Weil pairing gives det(conj) = -1
  ------------------------------------------------
  #E(ℝ)[m] ≤ 2m
```

## What not to use

Do not try to prove the fixed-point estimate by eigenvalues of `A` over `Z/mZ`.  That approach will keep running into non-field and two-primary pathologies.

Do not try to use

```text
det(A - I) = -tr(A)
```

as a cardinal formula.  Even when the identity is algebraically true, it does not control the kernel size over `Z/mZ` unless one tracks prime-power divisibility.

Also, do not rely on the topological statement

```text
E(ℝ)_0 ≃ S^1.
```

It gives a short proof, but it is not needed for this bound.

## Final recommendation

Use the Galois-conjugation route, but package the fixed-point step as the independent lemma

```text
A.det = -1  ⇒  #ker(A - I) ≤ m * gcd(m, 2).
```

This is the cleanest non-topological route.  It is algebraic, sharp, and isolates all hard elliptic-curve content into standard algebraic bridges: the `ZMod m` structure of complex torsion, real descent as fixed points, and the Weil-pairing determinant calculation.
