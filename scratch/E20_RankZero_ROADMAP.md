No:  
\[
E20:\ y^2=x^3+x^2+4x+4
\]
is **not** \(\mathbb Q\)-isomorphic to  
\[
C:\ w^2=u^3+u^2-u.
\]

The quick invariant obstruction is:
\[
j(E20)=\frac{21296}{25},\qquad \Delta(E20)=-6400,
\]
while
\[
j(C)=\frac{16384}{5},\qquad \Delta(C)=80.
\]
Since \(j\) differs, there is no `WeierstrassCurve.VariableChange ℚ` taking one model to the other. LMFDB also identifies your \(E20\) model as \(y^2=x^3+x^2+4x+4\), with discriminant \(-6400\), \(j=21296/25\), rank \(0\), torsion \(\mathbb Z/6\mathbb Z\), and affine integral points \((-1,0),(0,\pm2),(4,\pm10)\). citeturn113469view0 Mathlib’s `VariableChange` is exactly the \((u,r,s,t)\) admissible change \((X,Y)\mapsto (u^2X+r,u^3Y+u^2sX+t)\), and `variableChange_j` says \(j\) is invariant under it, so the unequal \(j\)’s are decisive. citeturn885277view0

The right relation is:

\[
E20 \xrightarrow{x=X-1} E_0:\ y^2=X^3-2X^2+5X
\]

and \(E_0\) is **2-isogenous** to

\[
E_2:\ Y^2=U^3+4U^2-16U,
\]

which is \(\mathbb Q\)-isomorphic to your obstruction curve \(C\) by scaling

\[
U=4u,\qquad Y=8w.
\]

At the `VariableChange` level, the two useful changes are:

```lean
def E20 : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 1,  a₃ := 0, a₄ := 4,   a₆ := 4 }

def E0 : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := -2, a₃ := 0, a₄ := 5,   a₆ := 0 }

def E2 : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 4,  a₃ := 0, a₄ := -16, a₆ := 0 }

def C20a4 : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 1,  a₃ := 0, a₄ := -1,  a₆ := 0 }

def shiftE20 : WeierstrassCurve.VariableChange ℚ :=
  { u := (1 : ℚˣ), r := -1, s := 0, t := 0 }

noncomputable def twoUnitQ : ℚˣ :=
  Units.mk0 (2 : ℚ) (by norm_num)

def scaleE2ToC : WeierstrassCurve.VariableChange ℚ :=
  { u := twoUnitQ, r := 0, s := 0, t := 0 }
```

Then the computational lemmas should be:

```lean
lemma shiftE20_smul : shiftE20 • E20 = E0 := by
  ext <;> norm_num [shiftE20, E20, E0,
    WeierstrassCurve.variableChange_def]

lemma scaleE2ToC_smul : scaleE2ToC • E2 = C20a4 := by
  ext <;> norm_num [scaleE2ToC, twoUnitQ, E2, C20a4,
    WeierstrassCurve.variableChange_def]
```

So: use `variableChangePointAddEquiv` only for `E20 ≃ E0` and `E2 ≃ C20a4`; it cannot directly bridge `E20` and `C20a4`.

The 2-isogeny from \(E_0\) to \(E_2\), with kernel \(\{\infty,(0,0)\}\), is the standard one for

\[
y^2=X^3+aX^2+bX,\qquad a=-2,\ b=5.
\]

For \(X\ne0\):

\[
\phi(X,y)=
\left(
\frac{y^2}{X^2},
\frac{y(5-X^2)}{X^2}
\right)
\in E_2.
\]

Composed with the scaling \(E_2\to C\), this is

\[
\Phi(X,y)=
\left(
u=\frac{y^2}{4X^2},
\quad
w=\frac{y(5-X^2)}{8X^2}
\right)
\in C.
\]

Define it in Lean by cases on `Point.zero`, affine points, and `X = 0`. Mathlib’s `Affine.Point` type has exactly `Point.zero` for infinity and `Point.some x y h` for nonsingular affine points; on elliptic curves you can build affine points with `Point.mk h`. citeturn460678view0turn460678view3

The key theorem you want is essentially:

```lean
lemma E0_point_cases (P : E0.toAffine.Point) :
    P = 0
  ∨ P = E0point 0 0
  ∨ P = E0point 1 2
  ∨ P = E0point 1 (-2)
  ∨ P = E0point 5 10
  ∨ P = E0point 5 (-10) := by
  -- cases P with
  -- | zero => ...
  -- | some X y h =>
  --     by_cases hX : X = 0
  --     · -- equation gives y = 0
  --     · -- form u,w as above
  --       -- prove w^2 = u^3 + u^2 - u by field_simp using h
  --       -- apply obstruction_20a4 u w
  --       -- cases u = -1,0,1
```

The algebra after `obstruction_20a4` is very small.

For \(X\ne0\), obstruction gives

\[
u=\frac{y^2}{4X^2}\in\{-1,0,1\}.
\]

Case \(u=-1\): impossible over \(\mathbb Q\), since \(y^2=-4X^2\) and \(X\ne0\).

Case \(u=0\): then \(y=0\), and the \(E_0\) equation gives

\[
X(X^2-2X+5)=0.
\]
Since \(X\ne0\), you get
\[
X^2-2X+5=(X-1)^2+4=0,
\]
impossible over \(\mathbb Q\).

Case \(u=1\): then \(y^2=4X^2\). Combining with

\[
y^2=X^3-2X^2+5X
\]
and \(X\ne0\), you get

\[
X^2-6X+5=0,
\]
hence

\[
(X-1)(X-5)=0.
\]

So \(X=1\) or \(X=5\). Then \(y=\pm2\) or \(y=\pm10\). Thus

\[
E_0(\mathbb Q)=
\{\infty,(0,0),(1,\pm2),(5,\pm10)\}.
\]

Transporting back by \(x=X-1\) gives exactly

\[
E20(\mathbb Q)=
\{\infty,(-1,0),(0,\pm2),(4,\pm10)\}.
\]

The image table under \(\Phi:E_0\to C\) is:

| \(C\)-point | rational preimages on \(E_0\) | corresponding \(E20\)-points |
|---|---:|---:|
| \(\infty\) | \(\infty,(0,0)\) | \(\infty,(-1,0)\) |
| \((1,1)\) | \((1,2),(5,-10)\) | \((0,2),(4,-10)\) |
| \((1,-1)\) | \((1,-2),(5,10)\) | \((0,-2),(4,10)\) |
| \((0,0)\) | none over \(\mathbb Q\) | none |
| \((-1,\pm1)\) | none over \(\mathbb Q\) | none |

So the obstruction curve’s affine \(u\)-values \(-1,0,1\) do **not** correspond bijectively to \(E20\)-points. Only the \(u=1\) target points have rational non-kernel preimages, and \(\infty\) has the two kernel preimages.

The shortest formal route is therefore:

```lean
-- 1. Shift E20 to E0 by VariableChange.
lemma shiftE20_smul : shiftE20 • E20 = E0 := ...

-- 2. Define the rational 2-isogeny-to-obstruction map on E0-points:
--    zero ↦ zero, (0,0) ↦ zero, and for X ≠ 0:
--    u = y^2 / (4*X^2), w = y*(5-X^2)/(8*X^2).

-- 3. Prove map lands on C20a4:
lemma phi_lands
  {X y : ℚ}
  (hX : X ≠ 0)
  (hE : y^2 = X^3 - 2*X^2 + 5*X) :
  let u := y^2 / (4*X^2)
  let w := y*(5 - X^2)/(8*X^2)
  w^2 = u^3 + u^2 - u := by
    field_simp [hX] at *
    ring_nf at *

-- 4. Apply obstruction_20a4 to get u ∈ {-1,0,1}.

-- 5. Solve the three cases by nlinarith / ring_nf:
--    u = -1 impossible,
--    u = 0 impossible unless X = 0,
--    u = 1 gives X = 1 or X = 5 and y = ±2 or ±10.

-- 6. Transport the finite list back from E0 to E20.
```

You can still call your integer-box completeness at the end, but it is not the essential route. The isogeny argument already gives the exact rational coordinates. If your existing final theorem is phrased as “all rational points with integral coordinates in the box are known,” then prove the intermediate corollary

```lean
lemma E20_rational_point_has_known_x
  (P : E20.toAffine.Point) :
  P = 0 ∨
  ∃ x y : ℚ,
    P = E20point x y ∧ x ∈ ({-1, 0, 4} : Finset ℚ) := ...
```

and let your box theorem finish the \(y\)-coordinates. But the direct finite-case proof is probably shorter.

The group structure is useful only as a sanity check. The visible points form a subgroup generated by \((4,10)\) of order \(6\), consistent with LMFDB’s \(\mathbb Z/6\mathbb Z\) report. citeturn113469view0 But “every point is a multiple of the generator” is exactly the missing completeness theorem; using it would repackage the hard part, not remove it.

The single hardest Lean step is the explicit rational-map lemma `phi_lands` plus the fiber case split around the denominator \(X=0\). Once that is in place, `obstruction_20a4`, `field_simp`, `ring_nf`, `nlinarith`, and the two `VariableChange` computations should discharge the rest.
