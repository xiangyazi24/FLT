## Honest verdict

The line-function/Miller route is the right construction route, but **not divisor-free** if you want a real `WeilPairingPackage` with bilinear, alternating, perfect, Galois-equivariant pairing. Mathlib gives enough explicit affine group-law infrastructure to define Miller functions as rational functions, but it does **not** currently give a bundled divisor/evaluation/Weil-reciprocity layer for those functions.

So the leanest realistic design is:

\[
\text{explicit line/vertical factors}
\to \text{formal Miller words}
\to \text{map to } k(E)=\operatorname{Frac}(k[E])
\to \text{minimal divisor/evaluation API for these words only}
\to \text{Weil pairing package}.
\]

Do **not** try to build this directly as arbitrary elements of `FunctionField` and then evaluate them. Use a syntactic “Miller expression” carrier with a semantic map to the function field.

---

# 1. Line functions

Mathlib does not appear to expose bundled rational functions

```lean
ℓ_{P,Q} : W.FunctionField
v_R     : W.FunctionField
```

as ready-made objects with divisor theorems. But it exposes exactly the ingredients you need:

```lean
WeierstrassCurve.Affine.linePolynomial
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.addY
WeierstrassCurve.Affine.CoordinateRing.XClass
WeierstrassCurve.Affine.CoordinateRing.YClass
```

`linePolynomial x y ℓ` is the polynomial

\[
\ell(X-x)+y,
\]

i.e. the right-hand side of the affine line \(Y=\ell(X-x)+y\). `slope` is the secant/tangent slope; it uses the tangent formula when the two affine points coincide and returns `0` in the vertical case. Mathlib’s docs explicitly state these formulas. citeturn929881view2turn929881view3

So define the actual line function as

\[
L_{x,y,\lambda}(X,Y)=Y-\bigl(\lambda(X-x)+y\bigr),
\]

using `YClass`, because `YClass W p` is the coordinate-ring element \(Y-p(X)\). Define the vertical line as

\[
V_x(X,Y)=X-x,
\]

using `XClass`, because `XClass W x` is the coordinate-ring element \(X-x\). Mathlib already has `XIdeal`, `YIdeal`, and `XYIdeal` built from these classes. citeturn929881view1

Lean shape:

```lean
namespace WeierstrassCurve.Affine.Miller

variable {k : Type*} [Field k] [DecidableEq k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

abbrev CoordRing := W.CoordinateRing
abbrev FunField  := W.FunctionField

noncomputable def lineCR (x y λ : k) : CoordRing W :=
  WeierstrassCurve.Affine.CoordinateRing.YClass W
    (WeierstrassCurve.Affine.linePolynomial x y λ)

noncomputable def verticalCR (x : k) : CoordRing W :=
  WeierstrassCurve.Affine.CoordinateRing.XClass W x

noncomputable def lineFF (x y λ : k) : FunField W :=
  algebraMap (CoordRing W) (FunField W) (lineCR W x y λ)

noncomputable def verticalFF (x : k) : FunField W :=
  algebraMap (CoordRing W) (FunField W) (verticalCR W x)
```

Mathlib’s affine function field is already

```lean
W.FunctionField = FractionRing W.CoordinateRing
```

and the coordinate ring is

```lean
W.CoordinateRing = AdjoinRoot W.polynomial.
```

This is exactly the carrier you want for semantic rational functions. citeturn929881view0

For affine points

```lean
P = .some x₁ y₁ h₁
Q = .some x₂ y₂ h₂
```

set

```lean
λ := W.slope x₁ x₂ y₁ y₂
```

and define

\[
\ell_{P,Q}=Y-\bigl(\lambda(X-x_1)+y_1\bigr).
\]

For the Miller step factor, use

\[
g_{P,Q}=
\begin{cases}
1, & P=O \text{ or } Q=O,\\
V_P, & Q=-P,\\
-\ell_{P,Q}/V_{P+Q}, & \text{otherwise}.
\end{cases}
\]

The minus sign is deliberate. With the usual local parameter at \(O\), \(x\sim t^{-2}\), \(y\sim -t^{-3}\), so

\[
\ell_{P,Q}/V_{P+Q}
\]

has leading coefficient \(-1\) at \(O\). Multiplying by \(-1\) makes the Miller step normalized at \(O\). This avoids the annoying global `(-1)^m` in the final pairing formula.

Lean shape:

```lean
noncomputable def gLineFF
    (A B : W.Point) : FunField W :=
  match A, B with
  | 0, _ => 1
  | _, 0 => 1
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
      if hvert : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then
        verticalFF W x₁
      else
        let λ := W.slope x₁ x₂ y₁ y₂
        match A + B with
        | 0 => verticalFF W x₁        -- should be unreachable under `¬ hvert`
        | .some x₃ y₃ h₃ =>
            - lineFF W x₁ y₁ λ / verticalFF W x₃
```

You will also want a syntactic version, not only the `FunctionField` version:

```lean
inductive MillerFactor
| line     (x y λ : k)
| vertical (x : k)
| const    (a : kˣ)

inductive MillerExpr
| one
| factor (F : MillerFactor)
| mul    (f g : MillerExpr)
| inv    (f : MillerExpr)
```

with

```lean
noncomputable def MillerExpr.toFF : MillerExpr → FunField W
noncomputable def MillerExpr.evalAffine :
    MillerExpr → W.Point → k   -- partial, with nonzero denominator hypotheses
```

The **syntactic expression** is the better primary object. The `FunctionField` element is only its semantic interpretation.

---

# 2. Miller functions

Use the normalized Miller recurrence.

For a fixed point \(P\), define \(f_{0,P}=1\), and recursively keep a state \(([n]P,f_{n,P})\):

```lean
noncomputable def millerState (P : W.Point) :
    ℕ → W.Point × MillerExpr
| 0 => (0, .one)
| n+1 =>
    let S := millerState n
    let R := S.1
    let f := S.2
    (R + P, .mul f (gLineExpr W R P))

noncomputable def millerExpr (P : W.Point) (n : ℕ) : MillerExpr :=
  (millerState W P n).2

theorem millerState_fst (P : W.Point) (n : ℕ) :
    (millerState W P n).1 = n • P := by
  induction n with
  | zero => simp [millerState]
  | succ n ih =>
      simp [millerState, ih, Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc]
```

This linear recurrence is much easier to formalize than a full addition-chain recurrence. Later, if performance matters, define a binary Miller algorithm and prove it semantically equal up to normalized divisor. For the theorem-proving architecture, linear recurrence is enough.

The divisor recurrence you want is:

\[
\operatorname{div}(g_{A,B})=[A]+[B]-[A+B]-[O].
\]

Then by induction,

\[
\operatorname{div}(f_{n,P})
=
n[P]-[[n]P]-(n-1)[O].
\]

Lean shape:

```lean
abbrev Divisor (W : WeierstrassCurve.Affine k) :=
  W.Point →₀ ℤ

notation "⟦" P "⟧" => Finsupp.single P (1 : ℤ)

def divExpr : MillerExpr → Divisor W
```

Key lemmas:

```lean
theorem div_gLineExpr (A B : W.Point) :
    divExpr W (gLineExpr W A B)
      = ⟦A⟧ + ⟦B⟧ - ⟦A + B⟧ - ⟦0⟧

theorem div_millerExpr (P : W.Point) (n : ℕ) :
    divExpr W (millerExpr W P n)
      = (n : ℤ) • ⟦P⟧ - ⟦n • P⟧ - ((n : ℤ) - 1) • ⟦0⟧
```

For \(P\in E[m]\), this becomes

\[
\operatorname{div}(f_{m,P})=m[P]-m[O].
\]

```lean
theorem div_millerExpr_of_mem_nTorsion
    {P : W.Point} {m : ℕ} (hP : m • P = 0) :
    divExpr W (millerExpr W P m)
      = (m : ℤ) • ⟦P⟧ - (m : ℤ) • ⟦0⟧ := by
  rw [div_millerExpr, hP]
  abel
```

This is the central invariant.

---

# 3. Evaluation and the actual pairing

Do **not** define evaluation first as a partial map

```lean
W.FunctionField → W.Point → k
```

That is painful because a fraction-field element has many numerator/denominator representatives, and evaluation is only defined when the chosen denominator is nonzero.

Instead, evaluate the **syntactic Miller expression**. For an affine point \(R=(x_R,y_R)\),

```lean
def MillerFactor.evalAffine : MillerFactor → W.Point → k
| .vertical x₀, .some x y h => x - x₀
| .line x₀ y₀ λ, .some x y h =>
    y - (λ * (x - x₀) + y₀)
| .const a, _ => a
| _, 0 => -- not affine; use local-at-O API if needed
```

For full Weil-pairing proofs you still need evaluation at \(O\), but keep it minimal:

```lean
def MillerFactor.ordAtO : MillerFactor → ℤ
def MillerFactor.lcAtO  : MillerFactor → kˣ
```

with primitive/local lemmas:

```lean
ordAtO_vertical : ordAtO (.vertical x) = -2
lcAtO_vertical  : lcAtO  (.vertical x) = 1

ordAtO_line_nonvertical : ordAtO (.line x y λ) = -3
lcAtO_line_nonvertical  : lcAtO  (.line x y λ) = -1
```

If you normalize `gLineExpr` with the minus sign above, you get

```lean
theorem lcAtO_gLineExpr (A B : W.Point) :
    lcAtO (gLineExpr W A B) = 1
```

and hence

```lean
theorem lcAtO_millerExpr (P : W.Point) (n : ℕ) :
    lcAtO (millerExpr W P n) = 1
```

This is a major simplification.

The proper Weil pairing definition should use degree-zero divisor evaluation, not raw point evaluation:

```lean
def evalDiv
    (f : MillerExpr)
    (D : Divisor W)
    (hdisj : DisjointSupport (divExpr W f) D) : kˣ :=
  ∏ R in D.support, evalAtAsUnit f R ^ D R
```

Then for \(P,Q\in E[m]\), choose auxiliary divisors

\[
D_P \sim [P]-[O],\qquad D_Q\sim [Q]-[O],
\]

with disjoint support from the relevant Miller divisors, and define

\[
e_m(P,Q)=\frac{f_{m,P}(D_Q)}{f_{m,Q}(D_P)}.
\]

Lean shape:

```lean
noncomputable def weilPairingRaw
    {m : ℕ} [NeZero m]
    (P Q : W.nTorsion m) :
    (rootsOfUnity m k) :=
  rootsOfUnity.mkOfPowEq
    (evalDiv ... / evalDiv ...)
    (weilPairingRaw_pow_eq_one W P Q)
```

Mathlib’s roots-of-unity target should be

```lean
rootsOfUnity m k
```

which is a subgroup of `kˣ`; membership simplifies to `ζ ^ m = 1`, and `rootsOfUnity.mkOfPowEq` builds a root of unity from a scalar with a proof of the power equation. citeturn466233view0

For the computational formula, prove a derived theorem:

```lean
theorem weilPairing_eq_miller_direct
    {m : ℕ} [NeZero m]
    {P Q : W.Point}
    (hPm : m • P = 0) (hQm : m • Q = 0)
    (hgood : MillerDirectGood W m P Q) :
    ((weilPairing W m ⟨P, hPm⟩ ⟨Q, hQm⟩ : rootsOfUnity m k) : kˣ)
      =
    Units.mk0
      ((millerExpr W P m).evalAffine Q /
       (millerExpr W Q m).evalAffine P)
      (by exact direct_value_ne_zero ...)
```

With normalized Miller functions, there is no `(-1)^m`. If you do not normalize the line/vertical quotient, expect a sign lemma of the form

\[
e_m(P,Q)=(-1)^m\,\frac{f_{m,P}(Q)}{f_{m,Q}(P)}
\]

or a nearby parity variant depending on your exact line convention.

For the FLT primitive-root step, this direct theorem is what you want to use after the abstract package proves perfection.

---

# 4. Required properties and their difficulty

### Easiest: Galois equivariance

This is the most compatible with the explicit Miller setup. The line functions are built from coordinates using field operations. Mathlib even has a base-change compatibility theorem for `slope`: the slope after applying a field map is the image of the original slope. citeturn576349view1

For function fields, Mathlib has the fraction-ring transport API:

```lean
IsFractionRing.ringEquivOfRingEquiv
IsFractionRing.semilinearEquivOfRingEquiv
IsFractionRing.algEquivOfAlgEquiv
```

These extend ring/algebra equivalences of coordinate rings to fraction fields. citeturn191076view2

For roots of unity, Mathlib has

```lean
restrictRootsOfUnity
MulEquiv.restrictRootsOfUnity
restrictRootsOfUnity_coe_apply
MulEquiv.restrictRootsOfUnity_coe_apply
```

so once you prove scalar equivariance, the target coercion into `rootsOfUnity m k` is clean. citeturn466233view0

Target theorem:

```lean
theorem weilPairing_galois
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    {m : ℕ} [NeZero m]
    (P Q : (W.baseChange L).nTorsion m) :
    weilPairing (W.baseChange L) m (σ • P) (σ • Q)
      =
    (σ.toMulEquiv.restrictRootsOfUnity m)
      (weilPairing (W.baseChange L) m P Q)
```

This should be mostly induction over `MillerExpr`, plus the `slope` base-change lemma.

### Medium-hard: lands in \(\mu_m\)

Once bilinearity is available, this is short:

\[
e_m(P,Q)^m=e_m(mP,Q)=e_m(0,Q)=1.
\]

Lean target:

```lean
theorem weilPairing_pow_eq_one
    {m : ℕ} [NeZero m]
    (P Q : W.nTorsion m) :
    ((weilPairing W m P Q : rootsOfUnity m k) : kˣ) ^ m = 1 := by
  simpa using (mem_rootsOfUnity m ((weilPairing W m P Q : rootsOfUnity m k) : kˣ)).mp
```

The hard part is not the final root-of-unity statement; it is bilinearity.

### Hard: bilinearity and alternating

The standard proof uses divisor evaluation and Weil reciprocity. You can formalize the proof without a full Picard group, but you need a minimal “principal divisor calculus” for Miller expressions.

Essential primitive:

```lean
theorem weil_reciprocity_millerExpr
    (f g : MillerExpr)
    (hdisj : DisjointSupport (divExpr W f) (divExpr W g)) :
    evalDiv f (divExpr W g) = evalDiv g (divExpr W f)
```

Once you have this, bilinearity is a normal textbook proof.

Target theorems:

```lean
theorem weilPairing_mul_left
    (P₁ P₂ Q : W.nTorsion m) :
    weilPairing W m (P₁ + P₂) Q
      = weilPairing W m P₁ Q * weilPairing W m P₂ Q

theorem weilPairing_mul_right
    (P Q₁ Q₂ : W.nTorsion m) :
    weilPairing W m P (Q₁ + Q₂)
      = weilPairing W m P Q₁ * weilPairing W m P Q₂

theorem weilPairing_self
    (P : W.nTorsion m) :
    weilPairing W m P P = 1

theorem weilPairing_skew
    (P Q : W.nTorsion m) :
    weilPairing W m Q P = (weilPairing W m P Q)⁻¹
```

Alternating follows from the same divisor argument plus normalization.

### Hardest: nondegeneracy/perfectness

This is the part I would **not** try to prove by direct explicit computation. The standard theorem is geometric:

\[
E[m]\times E[m]\to\mu_m
\]

is a perfect alternating pairing when \(\operatorname{char} k\nmid m\).

To prove this in Lean, use abstract group/cardinality facts after the pairing is constructed:

1. prove or import

```lean
Nat.card (W.nTorsion m) = m^2
```

over separably closed fields with `(m : k) ≠ 0`;

2. prove the left and right kernels of the pairing are trivial;

3. conclude perfection by cardinality.

Target theorem:

```lean
theorem weilPairing_left_nontrivial
    {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (P : W.nTorsion m) (hP : P ≠ 0) :
    ∃ Q : W.nTorsion m, weilPairing W m P Q ≠ 1
```

This is the real mathematical bottleneck. It is not helped much by the explicit line formulas.

---

# 5. Minimal Mathlib primitives to add

Here is the smallest useful stack.

## A. Syntactic Miller expressions

```lean
inductive MillerFactor
| line     (x y λ : k)
| vertical (x : k)
| const    (a : kˣ)

inductive MillerExpr
| one
| factor (F : MillerFactor)
| mul    (f g : MillerExpr)
| inv    (f : MillerExpr)
```

Definitions:

```lean
MillerFactor.toFF
MillerExpr.toFF
MillerFactor.evalAffine
MillerExpr.evalAffine
MillerFactor.ordAtO
MillerFactor.lcAtO
MillerExpr.ordAtO
MillerExpr.lcAtO
```

## B. Line and vertical divisor lemmas

These are local intersection facts.

```lean
theorem div_vertical
    (R : W.Point) :
    divExpr W (verticalFactor R)
      = ⟦R⟧ + ⟦-R⟧ - 2 • ⟦0⟧

theorem div_line_nonvertical
    (P Q : W.Point) (h : Q ≠ -P) :
    divExpr W (lineFactor W P Q)
      = ⟦P⟧ + ⟦Q⟧ + ⟦-(P + Q)⟧ - 3 • ⟦0⟧

theorem div_gLineExpr
    (P Q : W.Point) :
    divExpr W (gLineExpr W P Q)
      = ⟦P⟧ + ⟦Q⟧ - ⟦P + Q⟧ - ⟦0⟧
```

Mathlib’s affine group-law files already contain the polynomial factorization behind this: substituting the line into the Weierstrass equation gives roots at \(x_P,x_Q,x_{P+Q}\), and the docs expose the corresponding `addPolynomial`/`addX` infrastructure. citeturn929881view3turn576349view1

## C. Miller divisor theorem

```lean
theorem div_millerExpr
    (P : W.Point) (n : ℕ) :
    divExpr W (millerExpr W P n)
      = (n : ℤ) • ⟦P⟧ - ⟦n • P⟧ - ((n : ℤ) - 1) • ⟦0⟧
```

## D. Divisor evaluation

```lean
def evalDiv
    (f : MillerExpr)
    (D : Divisor W)
    (hdisj : DisjointSupport (divExpr W f) D) : kˣ
```

Core lemmas:

```lean
evalDiv_mul
evalDiv_inv
evalDiv_addDivisor
evalDiv_principal_eq_one_or_reciprocity
```

The clean primitive is:

```lean
theorem weil_reciprocity_millerExpr
    (f g : MillerExpr)
    (hdisj : DisjointSupport (divExpr W f) (divExpr W g)) :
    evalDiv f (divExpr W g) = evalDiv g (divExpr W f)
```

This is the single hardest new theorem if you want a real proof.

## E. Pairing package

```lean
structure WeilPairingPackage
    (k : Type*) [Field k]
    (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (m : ℕ) [NeZero m] where

  pairing :
    W.nTorsion m → W.nTorsion m → rootsOfUnity m k

  map_add_left :
    ∀ P₁ P₂ Q,
      pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q

  map_add_right :
    ∀ P Q₁ Q₂,
      pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂

  alternating :
    ∀ P, pairing P P = 1

  nondeg_left :
    ∀ P, (∀ Q, pairing P Q = 1) → P = 0

  nondeg_right :
    ∀ Q, (∀ P, pairing P Q = 1) → Q = 0

  galois_equivariant :
    -- better in a separate base-change structure;
    -- do not force this into the same base-field-only structure initially
    True
```

I would keep Galois equivariance in a separate structure over an extension:

```lean
structure WeilPairingGaloisPackage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (W : WeierstrassCurve.Affine K)
    (m : ℕ) [NeZero m] where

  pkg : WeilPairingPackage L (W.baseChange L) m

  galois :
    ∀ (σ : L ≃ₐ[K] L) P Q,
      pkg.pairing (σ • P) (σ • Q)
        =
      (σ.toMulEquiv.restrictRootsOfUnity m) (pkg.pairing P Q)
```

---

# 6. The construction order I recommend

### File 1: `Miller/LineFunctions.lean`

Definitions:

```lean
lineCR
verticalCR
lineFF
verticalFF
gLineExpr
gLineFF
```

Lemmas:

```lean
toFF_gLineExpr
evalAffine_line
evalAffine_vertical
map_line_under_algEquiv
map_vertical_under_algEquiv
map_gLine_under_algEquiv
```

### File 2: `Miller/Divisor.lean`

Define only what you need:

```lean
abbrev Divisor := W.Point →₀ ℤ

def degree : Divisor W → ℤ
def supportDisjoint : Divisor W → Divisor W → Prop
def evalDiv : MillerExpr → Divisor W → ...
```

Do **not** build full Weil divisors of arbitrary rational functions yet.

### File 3: `Miller/MillerFunction.lean`

Definitions:

```lean
millerState
millerExpr
```

Lemmas:

```lean
millerState_fst
div_gLineExpr
div_millerExpr
lcAtO_gLineExpr
lcAtO_millerExpr
eval_millerExpr_map
```

### File 4: `Miller/WeilReciprocity.lean`

This is the hard file.

Minimal theorem:

```lean
theorem weil_reciprocity_millerExpr
    (f g : MillerExpr)
    (hdisj : DisjointSupport (divExpr W f) (divExpr W g)) :
    evalDiv f (divExpr W g) = evalDiv g (divExpr W f)
```

You can prove it only for `MillerExpr`, by induction from line/vertical factors. That is much smaller than proving full Weil reciprocity for arbitrary function-field elements.

### File 5: `Miller/WeilPairing.lean`

Definition:

```lean
noncomputable def weilPairing :
    W.nTorsion m → W.nTorsion m → rootsOfUnity m k
```

Theorems:

```lean
weilPairing_map_add_left
weilPairing_map_add_right
weilPairing_alternating
weilPairing_galois
weilPairing_nontrivial_left
weilPairing_nontrivial_right
```

### File 6: `FLT/WeilPairingPrimitiveRoot.lean`

Use only the package:

```lean
theorem weil_pairing_primitive_root
    {m : ℕ} [NeZero m]
    (P Q : W.nTorsion m)
    (hbasis : IsZModBasis m P Q) :
    IsPrimitiveRoot
      (((WeilPairingPackage.pairing pkg P Q : rootsOfUnity m k) : kˣ) : k)
      m
```

For this theorem, you do not want to unfold Miller functions.

---

# 7. What not to do

Do not try to prove the whole pairing by direct `field_simp + ring` identities on raw rational functions. That works for fixed small modular-curve reductions, but the general Weil pairing theorem needs:

\[
\operatorname{div}(f_{m,P})=m[P]-m[O],
\]

degree-zero divisor evaluation, independence of auxiliary choices, bilinearity, and nondegeneracy. Those are not realistically obtained by raw rational-function simplification.

Do not make arbitrary `FunctionField` elements the main syntax. `FunctionField` is right semantically, but bad operationally for partial evaluation. Keep a formal expression tree and map it into `FunctionField`.

Do not chase `(-1)^m` unless necessary. Normalize each nonvertical Miller step by `-ℓ/v`. Then the leading coefficient at \(O\) is \(1\), and the direct formula becomes clean.

---

## Single hardest primitive

The single hardest primitive is:

```lean
theorem weil_reciprocity_millerExpr
    (f g : MillerExpr)
    (hdisj : DisjointSupport (divExpr W f) (divExpr W g)) :
    evalDiv f (divExpr W g) = evalDiv g (divExpr W f)
```

Everything else is manageable local algebra plus induction.

The second-hardest primitive is nondegeneracy/perfectness:

```lean
theorem weilPairing_left_nontrivial
    (hm : (m : k) ≠ 0)
    (P : W.nTorsion m) (hP : P ≠ 0) :
    ∃ Q, weilPairing W m P Q ≠ 1
```

For FLT, isolate that in the package. Once the package has perfection and Galois equivariance, the primitive-root theorem is short and should not unfold Miller at all.
