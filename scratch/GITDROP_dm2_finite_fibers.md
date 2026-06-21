# Q63: finite fibers of the elliptic-curve projective x-coordinate

The key Mathlib lemmas are:

* `Projectivization.mk_eq_mk_iff'`: two nonzero vectors define the same projective point iff one is a scalar multiple of the other.
* `WeierstrassCurve.Affine.Point.xRep_zero`, `xRep_some`, `xRep_ne_zero`: the normalized representatives are `[1:0]` for `0` and `[x:1]` for affine points.
* `WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff`: raw `xRep` equality is equivalent to `P = Q ∨ P = -Q`.

The small normalization lemma `xProj_eq_xProj_iff_xRep_eq_xRep` is the only projective-space bookkeeping: because Mathlib's `Point.xRep` representatives are normalized, projective equality of their classes forces literal equality of the vectors.

```lean
import Mathlib

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- The rational projective line used for the x-coordinate map. -/
abbrev P1Q : Type := Projectivization ℚ (Fin 2 → ℚ)

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚ]

/--
The projective x-coordinate map on rational points of a Weierstrass curve.
It sends the point at infinity to `[1:0]` and an affine point `(x,y)` to `[x:1]`.
-/
def xProj : (E⁄ℚ).Point → P1Q :=
  fun P => Projectivization.mk ℚ P.xRep P.xRep_ne_zero

/--
For the normalized representatives produced by `Point.xRep`, projective equality is literal
representative equality.
-/
lemma xProj_eq_xProj_iff_xRep_eq_xRep
    {P Q : (E⁄ℚ).Point} :
    xProj E P = xProj E Q ↔ P.xRep = Q.xRep := by
  constructor
  · intro h
    rcases
      (Projectivization.mk_eq_mk_iff' ℚ P.xRep Q.xRep
        P.xRep_ne_zero Q.xRep_ne_zero).mp h with
      ⟨a, ha⟩
    cases P with
    | zero =>
        cases Q with
        | zero =>
            simp
        | some x y hQ =>
            have ha1 : a = 0 := by
              have h1 := congr_fun ha 1
              simpa using h1
            have hbad : (0 : ℚ) = 1 := by
              have h0 := congr_fun ha 0
              simpa [ha1] using h0
            exfalso
            exact zero_ne_one hbad
    | some xP yP hP =>
        cases Q with
        | zero =>
            have hbad : (0 : ℚ) = 1 := by
              have h1 := congr_fun ha 1
              simpa using h1
            exfalso
            exact zero_ne_one hbad
        | some xQ yQ hQ =>
            have ha1 : a = 1 := by
              have h1 := congr_fun ha 1
              simpa using h1
            have hx : xQ = xP := by
              have h0 := congr_fun ha 0
              simpa [ha1] using h0
            ext i
            fin_cases i <;> simp [hx]
  · intro h
    simp [xProj, h]

/--
The projective x-coordinate map has finite fibers.  More precisely, once one point `P₀`
in a fiber is chosen, the fiber is contained in `{P₀, -P₀}`.
-/
theorem xRep_finite_fibers
    (x : P1Q) :
    {P : (E⁄ℚ).Point | xProj E P = x}.Finite := by
  classical
  by_cases hx : ∃ P : (E⁄ℚ).Point, xProj E P = x
  · rcases hx with ⟨P₀, hP₀⟩
    refine ((Set.finite_singleton P₀).union (Set.finite_singleton (-P₀))).subset ?_
    intro P hP
    have hproj : xProj E P = xProj E P₀ := hP.trans hP₀.symm
    have hxraw : P.xRep = P₀.xRep :=
      (xProj_eq_xProj_iff_xRep_eq_xRep (E := E)).mp hproj
    have hPQ : P = P₀ ∨ P = -P₀ :=
      (WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff).mp hxraw
    rcases hPQ with rfl | hneg
    · simp
    · simp [hneg]
  · have hempty : {P : (E⁄ℚ).Point | xProj E P = x} = ∅ := by
      ext P
      constructor
      · intro hP
        exact False.elim (hx ⟨P, hP⟩)
      · intro hP
        simpa using hP
    simpa [hempty]

end WeierstrassCurve
```
