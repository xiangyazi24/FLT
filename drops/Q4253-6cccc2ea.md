ANSWER Q4253 6cccc2ea

# Bottom line

For this specific Jacobian, the bad-reduction correction at \(2\) is completely concrete:

\[
\Phi_2(\mathbf F_2)\cong \mathbf Z/3\mathbf Z,
\qquad
\mathcal J^0_{\mathbf F_2}(\mathbf F_2)\cong \mathbf Z/7\mathbf Z,
\]

where \(\mathcal J/\mathbf Z_2\) is the Néron model of
\(J=\operatorname{Jac}(X_1(18))\). Hence

\[
J(\mathbf Q_2)/J_1(\mathbf Q_2)\cong \mathbf Z/21\mathbf Z,
\]

with \(J_1\) the formal kernel. Thus the exact exponent needed to enter the formal group is

\[
\boxed{e=21}.
\]

The formal filtration

\[
U_n:=\ker\!\left(\mathcal J^0(\mathbf Z_2)
   \longrightarrow \mathcal J^0(\mathbf Z/2^{n+1}\mathbf Z)\right)
\quad(n\ge 0)
\]

has \(U_0=J_1(\mathbf Q_2)\), satisfies

\[
[2]U_n\subseteq U_{n+1},
\qquad
\bigcap_{n\ge0}U_n=\{0\},
\]

and therefore closes the Mordell–Weil-finite-generation-free argument:

\[
J(\mathbf Q)=2J(\mathbf Q)
\Longrightarrow
21J(\mathbf Q)=0.
\]

Since the independently checked torsion subgroup is \(\mathbf Z/21\mathbf Z\), this gives
\(J(\mathbf Q)=J(\mathbf Q)_{\rm tors}\cong\mathbf Z/21\mathbf Z\) and rank zero.

The important qualification is architectural: the **finite local calculation is small**, but the theorem connecting a semistable curve model to the identity and component groups of its Jacobian's Néron model is genuinely new relative to Mathlib. A fixed-instance implementation is still far smaller than formalizing Mordell–Weil finite generation for abelian surfaces; a full general Néron-model library would not be small.

---

# 1. Concrete semistable model at \(2\)

The LMFDB integral model attached to `324.a.648.1` is

\[
C:\quad y^2+h(x)y=f(x),
\]

with

\[
h=x^3+x+1,
\qquad
f=x^5+2x^4+2x^3+x^2.
\]

This is the coefficient pair recorded as

```text
[[0,0,1,2,2,1], [1,1,0,1]]
```

in low-to-high coefficient order. It is birational over \(\mathbf Q\) to the even model in the question.

Set

\[
g=x^2+x+1,
\qquad
u=y+g.
\]

A direct polynomial calculation gives

\[
f-g^2+hg=2x^3g,
\]

and therefore the equation becomes

\[
\boxed{u(u+h)=2g(u+x^3).}
\tag{1}
\]

All of this is a `ring` proof in Lean.

## Special fibre

Reducing (1) modulo \(2\) gives

\[
u(u+h)=0.
\]

Thus the geometric special fibre consists of two rational components

\[
C_0:\ u=0,
\qquad
C_1:\ u+h=0.
\]

Both are copies of \(\mathbf P^1_{\mathbf F_2}\). Their intersection is

\[
u=0,\qquad h=x^3+x+1=0.
\]

The cubic \(h\) has no root in \(\mathbf F_2\), hence is irreducible. The intersection is therefore one closed point

\[
D=\operatorname{Spec}\mathbf F_8,
\]

which becomes three geometric intersection points over \(\overline{\mathbf F}_2\).

They are transverse. Indeed,

\[
h'=x^2+1
\]

is coprime to \(h\), and at an intersection point the right-hand factor in (1),

\[
g(u+x^3),
\]

reduces to \(gx^3\), which is nonzero modulo \(h\):

\[
\gcd(h,gx)=1.
\]

Consequently the completed local equation at each geometric node is of the form

\[
UV=2\varepsilon,
\qquad \varepsilon\in\mathbf Z_2^{\times},
\]

so the model is semistable with thickness one. The two components have distinct points at infinity; there is no additional edge in the dual graph.

Hence the geometric dual graph is the theta graph

```text
       e₀
   v₀ ===== v₁
       e₁
       e₂
```

with two vertices and three parallel edges. Frobenius fixes the vertices and cyclically permutes the three edges, because the nodes form the degree-three point \(D=\operatorname{Spec}\mathbf F_8\).

## Lean-level finite checks

These are all computational:

```lean
abbrev F2 := ZMod 2

def n18h2 : F2[X] := X^3 + X + 1
def n18g2 : F2[X] := X^2 + X + 1

lemma n18_h2_irreducible : Irreducible n18h2 := by
  -- cubic: check the two possible roots
  native_decide

lemma n18_h2_squarefree : IsCoprime n18h2 n18h2.derivative := by
  native_decide

lemma n18_shift_identity :
    n18f - n18g^2 + n18h * n18g = 2 * X^3 * n18g := by
  ring

lemma n18_node_unit :
    IsCoprime n18h2 (n18g2 * X) := by
  native_decide
```

The weighted-projective infinity chart is another small polynomial/Jacobian-criterion check.

---

# 2. The Néron special fibre

Let \(\mathcal J/\mathbf Z_2\) be the Néron model of \(J\), and write

\[
J_0(\mathbf Q_2)
 =\{P:\widetilde P\in\mathcal J^0_{\mathbf F_2}(\mathbf F_2)\},
\]

\[
J_1(\mathbf Q_2)
 =\ker\bigl(\mathcal J^0(\mathbf Z_2)	o
                 \mathcal J^0_{\mathbf F_2}(\mathbf F_2)\bigr).
\]

Thus \(J_1\) is the formal group, while \(J_0/J_1\) is the group of rational points of the connected special fibre.

For a regular semistable curve, Raynaud's description identifies:

1. the connected special fibre with the generalized Jacobian of the nodal special fibre;
2. the component group with the graph Jacobian/critical group of its dual graph.

For the present two-component model both pieces are elementary.

## 2.1 The identity component

The normalizations of both components are \(\mathbf P^1\), so there is no abelian part. The identity component is a two-dimensional torus.

A convenient description is

\[
\mathcal J^0_{\mathbf F_2}
 \cong
\left(\operatorname{Res}_{\mathbf F_8/\mathbf F_2}\mathbf G_m\right)
 /\mathbf G_m.
\tag{2}
\]

This follows directly from gluing line bundles on the two normalizations along the degree-three node. Its character lattice is the augmentation lattice

\[
\{(a_0,a_1,a_2)\in\mathbf Z^3:a_0+a_1+a_2=0\},
\]

and Frobenius acts by the three-cycle on the coordinates.

Taking \(\mathbf F_2\)-points in (2),

\[
\mathcal J^0_{\mathbf F_2}(\mathbf F_2)
 \cong \mathbf F_8^\times/\mathbf F_2^\times.
\]

Since \(\mathbf F_2^\times\) is trivial and \(\mathbf F_8^\times\) is cyclic of order seven,

\[
\boxed{J_0(\mathbf Q_2)/J_1(\mathbf Q_2)\cong\mathbf Z/7\mathbf Z.}
\]

Equivalently, on a basis of the augmentation lattice, Frobenius has characteristic polynomial

\[
T^2+T+1,
\]

so

\[
\#\mathcal J^0_{\mathbf F_2}(\mathbf F_2)
 =\det(2I-F)=7.
\]

This determinant route is particularly easy to formalize.

## 2.2 The component group

The theta graph has Laplacian

\[
L=\begin{pmatrix}3&-3\\-3&3\end{pmatrix}.
\]

Deleting one row and column gives the reduced Laplacian \((3)\). Therefore its critical group is

\[
\operatorname{coker}(\mathbf Z\xrightarrow{\,3\,}\mathbf Z)
 \cong\mathbf Z/3\mathbf Z.
\]

Frobenius fixes both vertices, so its action on this critical group is trivial. Hence the component group is the constant group

\[
\boxed{\Phi_2\cong\mathbf Z/3\mathbf Z,}
\]

and the Tamagawa number is

\[
\boxed{c_2=\#\Phi_2(\mathbf F_2)=3.}
\]

This is just a one-by-one Smith-normal-form calculation in Lean.

## 2.3 The quotient before the formal kernel

Smooth reduction and Lang's theorem give exact sequences

\[
0\longrightarrow J_1(\mathbf Q_2)
 \longrightarrow J_0(\mathbf Q_2)
 \longrightarrow \mathbf Z/7\mathbf Z
 \longrightarrow0,
\]

\[
0\longrightarrow J_0(\mathbf Q_2)
 \longrightarrow J(\mathbf Q_2)
 \longrightarrow \mathbf Z/3\mathbf Z
 \longrightarrow0.
\]

Consequently

\[
\#\bigl(J(\mathbf Q_2)/J_1(\mathbf Q_2)\bigr)=21.
\]

The quotient is abelian, and every abelian group of order \(3\cdot7\) is cyclic. Thus

\[
\boxed{J(\mathbf Q_2)/J_1(\mathbf Q_2)\cong\mathbf Z/21\mathbf Z.}
\]

In particular,

\[
\boxed{21P\in J_1(\mathbf Q_2)\quad\text{for every }P\in J(\mathbf Q_2).}
\tag{3}
\]

The exponent \(21\) is not merely a coarse product. It is minimal: the known rational \(21\)-torsion embeds into \(J(\mathbf Q_2)\), while the pro-\(2\) formal kernel has no nonzero odd-order torsion. Hence its image in the quotient has order \(21\).

---

# 3. Formal filtration and doubling

Because \(\mathcal J\) is smooth of relative dimension two at the identity, its formal completion has a two-dimensional commutative formal group law over \(\mathbf Z_2\). Choose integral parameters

\[
z=(z_1,z_2)
\]

at the identity. Then

\[
J_1(\mathbf Q_2)\simeq (2\mathbf Z_2)^2
\]

as a formal neighbourhood, and multiplication by two has the form

\[
[2](z)=2z+H(z),
\tag{4}
\]

where every coefficient of \(H\) is \(2\)-integral and every monomial in \(H\) has total degree at least two.

Define

\[
U_n=\{P\in J_1(\mathbf Q_2):
      z_i(P)\in2^{n+1}\mathbf Z_2\text{ for }i=1,2\}.
\]

Equivalently,

\[
U_n=\ker\!\left(\mathcal J^0(\mathbf Z_2)	o
       \mathcal J^0(\mathbf Z/2^{n+1}\mathbf Z)\right).
\]

## Doubling estimate

If \(z_i\in2^{n+1}\mathbf Z_2\), then:

- the linear term \(2z_i\) lies in \(2^{n+2}\mathbf Z_2\);
- every degree-at-least-two term lies in
  \(2^{2(n+1)}\mathbf Z_2\subseteq2^{n+2}\mathbf Z_2\).

Therefore

\[
\boxed{[2]U_n\subseteq U_{n+1}\qquad(n\ge0).}
\tag{5}
\]

Notice that no formal logarithm is needed. At \(p=2\), starting with the maximal ideal \(2\mathbf Z_2\) is exactly deep enough for the quadratic terms to gain the required extra power of two.

## Separatedness

If \(P\in\bigcap_nU_n\), then both formal coordinates are divisible by every power of two. Since

\[
\bigcap_{n\ge0}2^{n+1}\mathbf Z_2=\{0\},
\]

we have \(z(P)=0\), and injectivity of the formal chart gives \(P=0\). Thus

\[
\boxed{\bigcap_{n\ge0}U_n=\{0\}.}
\tag{6}
\]

---

# 4. Exact Mordell–Weil-FG-free lemma chain

Let

\[
\iota:J(\mathbf Q)\hookrightarrow J(\mathbf Q_2)
\]

be localization.

## Global input from the 2-descent certificate

The Kummer injection gives

\[
J(\mathbf Q)/2J(\mathbf Q)
 \hookrightarrow \operatorname{Sel}^{(2)}(J/\mathbf Q).
\]

Therefore a checked certificate proving the \(2\)-Selmer group trivial yields

\[
\forall P\in J(\mathbf Q),\ \exists Q\in J(\mathbf Q),\ 2Q=P.
\tag{7}
\]

No finite-generation theorem is used here.

Iterating (7), for every \(n\) choose \(Q_n\) with

\[
2^nQ_n=P.
\]

By (3),

\[
21\iota(Q_n)\in U_0.
\]

Applying (5) \(n\) times gives

\[
21\iota(P)
 =2^n\bigl(21\iota(Q_n)\bigr)
 \in U_n.
\]

This holds for every \(n\), so (6) gives

\[
21\iota(P)=0.
\]

Localization is injective, hence

\[
\boxed{21P=0\quad\text{for every }P\in J(\mathbf Q).}
\tag{8}
\]

Thus every rational point is torsion, and the rationalized Mordell–Weil group is zero. This proves rank zero without `Module.Finite ℤ J`.

## Abstract Lean theorem

```lean
namespace TwoAdicSeparated

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def TwoSurjective : Prop :=
  ∀ x : G, ∃ y : G, 2 • y = x

structure FiltrationCertificate where
  loc : G →+ H
  loc_injective : Function.Injective loc
  U : ℕ → AddSubgroup H
  e : ℕ
  e_ne_zero : e ≠ 0
  enter : ∀ x : G, e • loc x ∈ U 0
  double_step : ∀ n z, z ∈ U n → 2 • z ∈ U (n + 1)
  separated : ∀ z, (∀ n, z ∈ U n) → z = 0

lemma pow_two_mem
    (C : FiltrationCertificate (G := G) (H := H))
    {z : H} (hz : z ∈ C.U 0) :
    ∀ n, (2 ^ n) • z ∈ C.U n := by
  intro n
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      simpa [pow_succ, mul_nsmul] using C.double_step n _ ih

lemma roots_of_twoSurjective
    (h2 : TwoSurjective (G := G)) (x : G) :
    ∀ n, ∃ y, (2 ^ n) • y = x := by
  -- elementary induction
  sorry

theorem exponent_kills
    (C : FiltrationCertificate (G := G) (H := H))
    (h2 : TwoSurjective (G := G)) :
    ∀ x : G, C.e • x = 0 := by
  intro x
  apply C.loc_injective
  apply C.separated
  intro n
  obtain ⟨y, hy⟩ := roots_of_twoSurjective h2 x n
  have h0 : C.e • C.loc y ∈ C.U 0 := C.enter y
  have hn := C.pow_two_mem h0 n
  -- commute scalar multiplications and rewrite with hy
  simpa [map_nsmul, smul_smul, mul_comm, mul_left_comm, mul_assoc, hy] using hn

end TwoAdicSeparated
```

For N18, instantiate this with

```lean
C.e := 21
C.U := n18FormalLevel
```

and `enter` supplied by the local quotient computation.

---

# 5. The smallest Lean-checkable local certificate

The implementation should have two layers.

## Layer A: arithmetic-facing finite certificate

```lean
structure N18NeronAtTwoFiniteCertificate where
  JQ2 : Type*
  instAddCommGroupJQ2 : AddCommGroup JQ2

  J0 J1 : AddSubgroup JQ2

  Phi : Type*
  instPhiFintype : Fintype Phi
  instPhiAddCommGroup : AddCommGroup Phi
  componentReduction : JQ2 →+ Phi
  componentKernel : componentReduction.ker = J0
  phiEquiv : Phi ≃+ ZMod 3

  IdentityPts : Type*
  instIdentityPtsFintype : Fintype IdentityPts
  instIdentityPtsAddCommGroup : AddCommGroup IdentityPts
  identityReduction : J0 →+ IdentityPts
  identityKernel : identityReduction.ker =
    J1.comap J0.subtype
  identityEquiv : IdentityPts ≃+ ZMod 7
```

The immediate consequence is:

```lean
lemma twentyOne_smul_mem_formal
    (C : N18NeronAtTwoFiniteCertificate) (P : C.JQ2) :
    21 • P ∈ C.J1 := by
  -- 3 kills the component image, then 7 kills the connected reduction
  sorry
```

For the absolute smallest downstream API, collapse the two exact sequences into one finite quotient:

```lean
structure N18LocalFiniteQuotient where
  red : J18Q2 →+ ZMod 21
  surjective : Function.Surjective red
  ker_red : red.ker = n18FormalKernel
```

This direct form is ideal for the final theorem. The decomposed `ZMod 3` and `ZMod 7` certificate is preferable while verifying the Néron calculation because it mirrors the geometry and makes mistakes easier to detect.

## Layer B: formal-kernel certificate

Mathlib's current `RingTheory.FormalGroup` API is one-dimensional. The smallest new reusable object needed here is not a full theory of formal Lie groups, but a two-coordinate duplication chart:

```lean
structure TwoDimIntegralFormalChart
    (A : Type*) [AddCommGroup A] where
  kernel : AddSubgroup A
  coord : kernel ≃ {z : Fin 2 → ℤ_[2] // ∀ i, z i ∈ (2 : ℤ_[2]) • ⊤}

  higher : Fin 2 → MvPowerSeries (Fin 2) ℤ_[2]
  higher_order_two : ∀ i, 2 ≤ (higher i).order

  dup_formula : ∀ P i,
    coord ⟨2 • P.1, by exact kernel.nsmul_mem P.2 2⟩ i =
      2 * coord P i +
        MvPowerSeries.eval₂Hom ... (higher i)
```

In practice it may be simpler to encode the already-proved valuation consequence rather than a general `order` API:

```lean
structure N18FormalAtTwoCertificate where
  U : ℕ → AddSubgroup J18Q2
  U_zero : U 0 = n18FormalKernel
  double_step : ∀ n P, P ∈ U n → 2 • P ∈ U (n + 1)
  separated : ∀ P, (∀ n, P ∈ U n) → P = 0
```

The stronger chart object is reusable and makes the certificate independently checkable. The smaller filtration object is suitable only after the explicit duplication-coordinate proof has been completed in the same trusted Lean development.

---

# 6. What is finite computation, and what is genuinely hard?

## Already in Mathlib or routine

- integer, rational, `ZMod 2`, and finite-field polynomial arithmetic;
- quotient/adjoin-root construction of \(\mathbf F_8\);
- irreducibility and gcd checks over a finite field;
- matrices, determinants, cokernels, and Smith normal form in this one-by-one case;
- finite enumeration of \(\mathbf F_8^\times\);
- `pAdicInt`, powers of the maximal ideal, and valuation separatedness;
- additive quotient groups and the abstract `exponent_kills` argument;
- polynomial identities by `ring`/`ring_nf`;
- finite assertions by `native_decide` or `decide`.

## New but moderate

1. A two-dimensional integral formal group/duplication chart.
2. The lemma that a smooth two-dimensional group over \(\mathbf Z_2\) has formal coordinates whose multiplication-by-two map is
   \(2z+\) terms of degree at least two.
3. The reduction exact sequence for the fixed smooth local group model.
4. A fixed semistable-model certificate format: components, nodes, thickness, dual graph, and Frobenius permutation.

## The main hard bridge

One needs a theorem of Raynaud type saying that for the Jacobian of a regular semistable curve:

- the Néron identity component is the generalized Jacobian of the special fibre;
- its torus is obtained from the dual graph/normalization gluing data;
- the component group is the critical group of the dual graph.

Mathlib does not presently supply this Jacobian/Néron infrastructure. Formalizing this theorem in full generality is substantial.

There are two realistic ways to keep the project small:

### Route 1 — small reusable semistable-Jacobian theorem

Formalize only the two-component, thickness-one case needed here:

```lean
theorem neron_data_of_two_P1_three_nodes
    (X : TwoComponentSemistableModel R)
    (hcomponents : ...)
    (hnodes : X.nodeScheme ≃ Spec F8) :
    (X.jacobianNeron.identitySpecial ≃
       (WeilRestriction F8 F2 Gm) ⧸ diagonalGm)
    ∧ (X.jacobianNeron.componentGroup ≃+ ZMod 3)
```

This is mathematically reusable but avoids a general theory of arbitrary weighted graphs and Picard functors.

### Route 2 — explicit local Mumford atlas

Avoid naming a Néron model. Using the generalized Mumford representation already required for the 2-descent project:

1. enumerate the 21 residue classes of \(J(\mathbf Q_2)/J_1\);
2. define a reduction-code homomorphism into `ZMod 21`;
3. prove its kernel is one explicit formal chart;
4. verify the duplication valuation estimate from explicit rational formulas.

This replaces the Raynaud theorem by a larger fixed calculation. It is less elegant, but it may be easier to integrate with an existing explicit genus-two arithmetic codebase.

---

# 7. Is it genuinely smaller than Mordell–Weil finite generation?

## Yes, under the fixed-instance architecture

The local proof needs only:

- one semistable model at one prime;
- a two-vertex graph;
- one degree-three finite field;
- a finite quotient of order 21;
- the first-order and degree-at-least-two shape of one formal duplication map.

By contrast, Mordell–Weil finite generation for an abelian surface requires a global height machine or an equivalent global descent-plus-height argument: projective embeddings, local/global heights, Northcott finiteness, weak Mordell–Weil, and the descent step. That is vastly larger.

## No, if the plan is “formalize all Néron models first”

A general library of Néron models, relative Picard functors, semistable reduction, and Raynaud's component-group theorem is itself a major algebraic-geometry project. The route is smaller only if the interface is deliberately specialized:

```text
fixed semistable genus-2 model
        ↓ finite checks
(two P¹s, degree-3 node, theta graph)
        ↓ one specialized Raynaud bridge
Phi₂ = Z/3, identity points = Z/7
        ↓
J(Q₂)/formal kernel = Z/21
        ↓ elementary 2-adic filtration
21 kills J(Q)
```

This is the recommended architecture.

---

# 8. Recommended bottom-up build order

1. **Local integral model.** Define \(f,h,g\), prove the shift identity, and verify the infinity chart.
2. **Semistability certificate.** Prove the two components, irreducible degree-three node, transversality, and thickness one.
3. **Graph layer.** Define the theta graph; compute its reduced Laplacian and critical group `ZMod 3`.
4. **Torus layer.** Construct the gluing torus or just its character lattice; compute Frobenius polynomial \(T^2+T+1\) and its \(\mathbf F_2\)-point group `ZMod 7`.
5. **Specialized Néron/Raynaud bridge.** Obtain the two reduction exact sequences.
6. **Finite quotient theorem.** Prove
   `J18Q2 / n18FormalKernel ≃+ ZMod 21` and hence `21 • P ∈ n18FormalKernel`.
7. **Two-dimensional formal chart.** Define \(U_n\), prove `double_step` and `separated`.
8. **Abstract group lemma.** Combine two-surjectivity with the local filtration to prove `∀ P, 21 • P = 0`.
9. **Global arithmetic conclusion.** Use the existing torsion certificate to identify
   `J18Q ≃+ ZMod 21`, then enumerate Abel–Jacobi images and recover the six cusps.

---

# 9. Concrete data summary

```text
Prime:                         2
Reduction type:                semistable, totally toric rank 2
Minimal local model:           y² + (x³+x+1)y = x⁵+2x⁴+2x³+x²
Special fibre:                 two P¹ components
Intersection scheme:           Spec(F₈)
Geometric dual graph:          two vertices, three parallel edges
Frobenius on edges:            a 3-cycle
Identity component:            (Res_{F₈/F₂} Gm) / Gm
Identity-component F₂-points:  Z/7
Component group Phi₂:          Z/3
Tamagawa number c₂:            3
J(Q₂)/formal kernel:           Z/21
Entry exponent e:              21
Formal levels:                 coordinates in (2^(n+1) Z₂)²
Doubling:                      [2]U_n subset U_(n+1)
Intersection:                  intersection U_n = 0
Global consequence:            Sel₂=0 => J(Q)=2J(Q) => 21 J(Q)=0
```

# References and reproducibility

- LMFDB record: <https://www.lmfdb.org/Genus2Curve/Q/324/a/648/1>
- Exact integral model/torsion data mirror: <https://github.com/maathilde-k/Mod-5-Galois-Images-of-Genus-2-Abelian-Curves/blob/0e01e8ed54d5525600853fa07801013726bd31bf/LMFDB_atypical_data.m#L13-L17>
- Published Magma torsion verification: <https://github.com/isogeny-primes/quadratic-torsion/blob/00f07b36f8978ae0b510004bd79f360e9924a642/magma_scripts/torsionVerifications.m>
- Corresponding log: <https://github.com/isogeny-primes/quadratic-torsion/blob/00f07b36f8978ae0b510004bd79f360e9924a642/logs/torsionVerifications_log.txt>
- Raynaud/Néron-model context: Jordan–Ribet–Scholl, *Modular curves and Néron models of generalized Jacobians*, <https://arxiv.org/abs/2207.13203>
- Current Mathlib one-dimensional formal-group API: <https://github.com/leanprover-community/mathlib4/blob/4efb186f102ebfd2eea1545c151d6fbcfdff0e43/Mathlib/RingTheory/FormalGroup/Basic.lean>
