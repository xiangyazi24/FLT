# Q513 (dm3): proving `(X0-X1)^3 | formalAddX` by chord-variable factoring

## Check result

Yes: Mathlib has the useful refactored theorem, named

```lean
WeierstrassCurve.Projective.addX_eq'
```

in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

But the theorem is slightly weaker/different from the naive hope.  It does **not** say that bare `addX` is definitionally a cubic polynomial in the chord variables.  The raw definition of `addX` is still the explicit homogeneous degree-4 polynomial.  The factored theorem says:

```lean
lemma addX_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a1 * (P y * Q z - Q y * P z) * P z * Q z
            * (P x * Q z - Q x * P z)
        - W'.a2 * P z * Q z * (P x * Q z - Q x * P z) ^ 2
        - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2)
        * (P x * Q z - Q x * P z)
```

Mathlib also has the analogous denominator-cleared theorem for `addZ`:

```lean
lemma addZ_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3
```

and `addXYZ_X` is just `rfl`, so the X-coordinate of `addXYZ` is exactly `addX`.

Important naming warning: Mathlib's `addU` is **not** the chord variable `U = Px*Qz - Qx*Pz`.  Mathlib's `addU` is the scalar

```lean
-(P y * Q z - Q y * P z)^3 / (P z * Q z)
```

over a field.  For this proof, define local names such as `formalU` and `formalV`; do not reuse `addU`.

## Consequence for the formal point

Let

```lean
P0 = P(t0) = ![t0, -1, w0]
P1 = P(t1) = ![t1, -1, w1]
```

and define

```lean
def formalU : FG2 K := P0 x * P1 z - P1 x * P0 z
-- = t0*w1 - t1*w0

def formalV : FG2 K := P0 y * P1 z - P1 y * P0 z
-- = (-1)*w1 - (-1)*w0 = w0 - w1
```

depending on the order convention, these may be negated.  The sign is irrelevant for divisibility by `delta^3`.

Let

```lean
def delta : FG2 K := X0 - X1
```

or the opposite sign.  From the earlier diagonal-difference lemmas:

```lean
theorem delta_dvd_formalU : delta | formalU := ...
theorem delta_dvd_formalV : delta | formalV := ...
```

The right hand side of `addX_eq'` is cubic in `formalU` and `formalV`:

```text
(V^2 * PzQz
 + a1 * V * PzQz * U
 - a2 * PzQz * U^2
 - PxQz * U^2
 - QxPz * U^2) * U
```

Each term contains total `U,V` degree at least 3:

```text
V^2 * U,
V * U^2,
U^3,
U^3,
U^3.
```

Therefore `(X0-X1)^3` divides the RHS, and hence

```lean
delta^3 | formalAddX * (w0*w1)^2
```

not immediately `delta^3 | formalAddX`.

The remaining step is exactly the Q499 cancellation: cancel `(w0*w1)^2` because it has difference-order zero.  Under the difference coordinate change

```text
X0 = S + H,
X1 = S,
delta = H,
```

the `H`-constant coefficient of `(w0*w1)^2` is

```text
(w(S)^2)^2 = w(S)^4 != 0.
```

So the one-variable `PowerSeries.X^n` cancellation lemma from Q499 applies.

## Lean implementation skeleton

First expose the formal chord variables and the denominator-cleared RHS.

```lean
namespace FormalGroupW

open MvPowerSeries WeierstrassCurve.Projective

variable {K : Type*} [Field K]

abbrev FG2 := MvPowerSeries (Fin 2) K

-- Choose the sign convention once and keep it everywhere.
def delta : FG2 K := MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)

noncomputable def P0 : Fin 3 -> FG2 K := formalP0
noncomputable def P1 : Fin 3 -> FG2 K := formalP1

local notation "x" => (0 : Fin 3)
local notation "y" => (1 : Fin 3)
local notation "z" => (2 : Fin 3)

noncomputable def w0 : FG2 K := P0 (K := K) z
noncomputable def w1 : FG2 K := P1 (K := K) z

noncomputable def formalU : FG2 K :=
  P0 (K := K) x * P1 (K := K) z - P1 (K := K) x * P0 (K := K) z

noncomputable def formalV : FG2 K :=
  P0 (K := K) y * P1 (K := K) z - P1 (K := K) y * P0 (K := K) z

noncomputable def formalAddX : FG2 K :=
  W.addX (P0 (K := K)) (P1 (K := K))

noncomputable def formalAddXRhs : FG2 K :=
  ((formalV (K := K)^2 * (w0 (K := K) * w1 (K := K))
    + W.a1 * formalV (K := K) * (w0 (K := K) * w1 (K := K)) * formalU (K := K)
    - W.a2 * (w0 (K := K) * w1 (K := K)) * formalU (K := K)^2
    - P0 (K := K) x * P1 (K := K) z * formalU (K := K)^2
    - P1 (K := K) x * P0 (K := K) z * formalU (K := K)^2)
    * formalU (K := K))
```

The precise coefficient names are probably `W.a1`, `W.a2` or `W'.a1`, `W'.a2` depending on how `FormalGroupW.lean` names the base-changed projective curve.  Use the names already present in that file.

Then instantiate Mathlib's theorem.

```lean
theorem formalAddX_mul_w0w1_sq_eq_rhs :
    formalAddX (W := W) * (w0 (W := W) * w1 (W := W))^2 =
      formalAddXRhs (W := W) := by
  -- `hP0` and `hP1` are the formal curve-equation proofs for the two substituted points.
  have h := W.addX_eq' (P := P0 (W := W)) (Q := P1 (W := W)) hP0 hP1
  -- h has exactly the desired denominator-cleared shape.
  -- Reduce `P0 z`, `P1 z`, `P0 x`, `P1 x`, etc. to `w0`, `w1`, `t0`, `t1`.
  simpa [formalAddX, formalAddXRhs, formalU, formalV, w0, w1, P0, P1, mul_assoc, mul_left_comm,
    mul_comm] using h
```

Now prove the cubic divisibility of the RHS.

```lean
lemma delta_pow3_dvd_formalAddXRhs
    (hU : delta (K := K) | formalU (W := W))
    (hV : delta (K := K) | formalV (W := W)) :
    delta (K := K)^3 | formalAddXRhs (W := W) := by
  rcases hU with ⟨U1, hU⟩
  rcases hV with ⟨V1, hV⟩
  subst hU
  subst hV
  refine ⟨_, ?_⟩
  ring
```

If `subst hU` does not work cleanly, use

```lean
  rw [hU, hV]
  refine ⟨_, ?_⟩
  ring
```

or define the quotient explicitly.  If `ring` is too slow, split into five terms and use `dvd_add`, `dvd_sub`, and `dvd_mul_of_dvd_right/left`.

This gives the denominator-cleared divisibility:

```lean
theorem delta_pow3_dvd_formalAddX_mul_w0w1_sq :
    delta (K := K)^3 | formalAddX (W := W) * (w0 (W := W) * w1 (W := W))^2 := by
  rw [formalAddX_mul_w0w1_sq_eq_rhs]
  exact delta_pow3_dvd_formalAddXRhs
    (delta_dvd_formalU (W := W))
    (delta_dvd_formalV (W := W))
```

Finally cancel `(w0*w1)^2` using the Q499 difference-coordinate cancellation lemma.

```lean
theorem delta_pow3_dvd_formalAddX :
    delta (K := K)^3 | formalAddX (W := W) := by
  apply delta_pow3_dvd_cancel_right_of_diffConst_ne_zero
    (B := (w0 (W := W) * w1 (W := W))^2)
  · -- diff-coordinate constant coefficient is w(S)^4, nonzero
    exact diffCoord_w0w1_sq_constCoeff_ne_zero (W := W)
  · exact delta_pow3_dvd_formalAddX_mul_w0w1_sq (W := W)
```

The cancellation lemma can be the Q499 theorem in the form:

```lean
theorem delta_pow_dvd_cancel_right_diffConst_ne_zero
    {A B : FG2 K} {n : Nat}
    (hB0 : diffConstCoeff B != 0)
    (h : delta^n | A * B) :
    delta^n | A
```

or the transported one-variable statement in `(K[[S]])[[H]]`.

## Practical file split

Suggested atom files:

1. `scratch/FormalGroupW_AddXFactored.lean` -- define `formalU`, `formalV`, `formalAddXRhs`, prove `formalAddX_mul_w0w1_sq_eq_rhs` from `Projective.addX_eq'`.  Estimated 60-120 lines.
2. `scratch/FormalGroupW_AddXDivCleared.lean` -- prove `delta^3 | formalAddXRhs`, hence `delta^3 | formalAddX*(w0*w1)^2`.  Estimated 50-100 lines.
3. `scratch/FormalGroupW_AddXCancel.lean` -- reuse Q499 cancellation to prove `delta^3 | formalAddX`.  Estimated 30-70 lines.

## Final answer

Use `Projective.addX_eq'`.  It is exactly the denominator-cleared chord-variable factorization needed for the proof.  However, it proves cubic divisibility for

```text
formalAddX * (w0*w1)^2
```

not directly for `formalAddX`.  Therefore the full proof is:

```text
delta | formalU,
delta | formalV
=> delta^3 | formalAddXRhs
=> delta^3 | formalAddX * (w0*w1)^2
=> delta^3 | formalAddX         -- by Q499 cancellation
```

Do not try to prove a new raw factored definition of `addX`; Mathlib's `addX_eq'` is the right theorem.  Also do not use Mathlib's `addU` as the chord variable: define local `formalU = Px*Qz - Qx*Pz` and `formalV = Py*Qz - Qy*Pz` instead.
