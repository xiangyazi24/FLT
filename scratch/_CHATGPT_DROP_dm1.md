# Q795 (dm1): formula-level projective `nsmul` over `CommRing`

## Short answer

The naive recursion using only

```lean
W.addXYZ accumulator P
```

is the wrong formula-level operation.  `addXYZ` is the off-diagonal secant formula.  In Mathlib's projective formula file it is explicitly documented/proved to return `![0, 0, 0]` on equal representatives:

```lean
lemma WeierstrassCurve.Projective.addXYZ_self (P : Fin 3 → R) :
    W'.addXYZ P P = ![0, 0, 0]
```

So using `addXYZ` recursively will indeed break as soon as the accumulated representative is projectively equivalent to the input point.

The clean formula-level operation is:

```lean
if P ≈ Q then W.dblXYZ P else W.addXYZ P Q
```

This is exactly the representative-level operation called `WeierstrassCurve.Projective.add` in

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
```

but if you want to import only `Projective.Formula`, define the same branch locally.  This works over any `CommRing R`; therefore it also works after setting `R := DualNumber K`, assuming the usual `CommRing` instance for the dual numbers is in scope.

## Compilable Lean code, using only `Projective.Formula`

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

noncomputable section

namespace WeierstrassCurve.Projective

universe u

variable {R : Type u} [CommRing R]

/-- The point at infinity, as a projective representative. -/
def formulaO : Fin 3 → R :=
  ![0, 1, 0]

/--
Formula-level projective addition on representatives.

This is the safe formula-level version: use the tangent/doubling formula on the diagonal and
use the secant/addition formula off the diagonal.

With `import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point`, this is Mathlib's
representative-level `W.add`.
-/
def formulaAdd (W : WeierstrassCurve.Projective R) (P Q : Fin 3 → R) : Fin 3 → R := by
  classical
  exact if P ≈ Q then W.dblXYZ P else W.addXYZ P Q

/-- Formula-level repeated addition of a projective representative. -/
def formulaNSmul (W : WeierstrassCurve.Projective R) :
    ℕ → (Fin 3 → R) → (Fin 3 → R)
  | 0, _ => formulaO
  | n + 1, P => formulaAdd W (formulaNSmul W n P) P

@[simp]
theorem formulaNSmul_zero (W : WeierstrassCurve.Projective R) (P : Fin 3 → R) :
    formulaNSmul W 0 P = formulaO :=
  rfl

@[simp]
theorem formulaNSmul_succ (W : WeierstrassCurve.Projective R) (n : ℕ) (P : Fin 3 → R) :
    formulaNSmul W (n + 1) P = formulaAdd W (formulaNSmul W n P) P :=
  rfl

@[simp]
theorem formulaNSmul_one (W : WeierstrassCurve.Projective R) (P : Fin 3 → R) :
    formulaNSmul W 1 P = formulaAdd W (formulaO : Fin 3 → R) P :=
  rfl

/-- Doubling the formula-level point at infinity returns the point at infinity, by direct evaluation. -/
@[simp]
theorem dblXYZ_formulaO (W : WeierstrassCurve.Projective R) :
    W.dblXYZ (formulaO : Fin 3 → R) = formulaO := by
  ext i <;> fin_cases i <;>
    simp [formulaO, dblXYZ, dblX, dblY, dblZ, negDblY, negY] <;>
    ring1

@[simp]
theorem formulaAdd_formulaO_formulaO (W : WeierstrassCurve.Projective R) :
    formulaAdd W (formulaO : Fin 3 → R) formulaO = formulaO := by
  classical
  rw [formulaAdd, if_pos (Setoid.refl _), dblXYZ_formulaO]

@[simp]
theorem formulaNSmul_formulaO (W : WeierstrassCurve.Projective R) (n : ℕ) :
    formulaNSmul W n (formulaO : Fin 3 → R) = formulaO := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [formulaNSmul_succ, ih, formulaAdd_formulaO_formulaO]

/--
For `1 • P`, the result is the raw `addXYZ` formula only in the genuinely off-diagonal case.
This is the corrected version of the proposed statement `formulaNSmul W 1 P = W.addXYZ O P`.
-/
theorem formulaNSmul_one_eq_addXYZ_of_not_equiv_formulaO
    (W : WeierstrassCurve.Projective R) {P : Fin 3 → R}
    (hP : ¬ (formulaO : Fin 3 → R) ≈ P) :
    formulaNSmul W 1 P = W.addXYZ (formulaO : Fin 3 → R) P := by
  classical
  rw [formulaNSmul_one, formulaAdd, if_neg hP]

/--
On the diagonal case for `1 • P` with `P ≈ O`, the safe formula uses `dblXYZ O`, not `addXYZ O P`.
-/
theorem formulaNSmul_one_eq_dblXYZ_of_equiv_formulaO
    (W : WeierstrassCurve.Projective R) {P : Fin 3 → R}
    (hP : (formulaO : Fin 3 → R) ≈ P) :
    formulaNSmul W 1 P = W.dblXYZ (formulaO : Fin 3 → R) := by
  classical
  rw [formulaNSmul_one, formulaAdd, if_pos hP]

end WeierstrassCurve.Projective
```

## Why the originally requested statement (2) needs correction

For the safe definition above, the unconditional statement

```lean
formulaNSmul W 1 P = W.addXYZ ![0, 1, 0] P
```

is not the right theorem.  If `P = ![0, 1, 0]`, then the right side is the raw diagonal secant formula, hence degenerates to `![0, 0, 0]`.  The safe formula instead chooses `dblXYZ ![0, 1, 0]`, which directly evaluates to `![0, 1, 0]`.

So the correct first-step theorem is the one in the code:

```lean
formulaNSmul W 1 P = formulaAdd W formulaO P
```

and the raw-`addXYZ` version is valid only with the off-diagonal hypothesis:

```lean
¬ (formulaO : Fin 3 → R) ≈ P
```

## If importing `Projective.Point` is allowed

Mathlib already has the representative-level branch:

```lean
noncomputable def WeierstrassCurve.Projective.add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q
```

This declaration is over `[CommRing R]`.  It is not the field-level group law on nonsingular points; it is the formula-level operation on representatives.  The nonsingular point group law appears later in the same file and needs the point/nonsingularity infrastructure.

Thus, with

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
```

you can replace `formulaAdd W A B` by `W.add A B` in the recursive definition.

## Binary expansion note

A binary-recursive version is fine only if every addition branch uses the same safe operation.  This is safe:

```text
nsmul (2k)   P = dblXYZ (nsmul k P)
nsmul (2k+1) P = formulaAdd W (dblXYZ (nsmul k P)) P
```

But this is still unsafe:

```text
nsmul (2k+1) P = addXYZ (dblXYZ (nsmul k P)) P
```

because `dblXYZ (nsmul k P)` can be projectively equivalent to `P`, for example at torsion points or in small characteristic/special fibers.  The diagonal problem is not specific to unary recursion; it is a problem with using raw `addXYZ` as if it were a total addition law.
