# P1 monotone stationary root-pinning: hard steps in Lean-ready detail

## Executive verdict

The monotone root-pinning route is sound, with two nontrivial analytic inputs:

1. **Derivative vanishing at infinity.** If `W` is antitone, bounded, `C^2`, and `W''` is bounded, then `W' -> 0` at both ends. This is a one-dimensional Barbalat-type lemma. Mathlib does not appear to provide Barbalat's lemma as a ready theorem, so prove it locally. The clean proof is by contradiction: if `|W'|` stays above a positive threshold along a sequence escaping to infinity, bounded `W''` gives fixed-width intervals on which `|W'|` remains positive; monotonicity makes these intervals produce a fixed drop in `W`; infinitely many disjoint drops contradict boundedness.

2. **Resolver at a constant limit.** If `W(x) -> L` at an end and `W` is bounded, then the whole-line elliptic resolver `V[W]` satisfies `V[W](x) -> (nu/mu) * L^gamma` and `V'[W](x) -> 0`. This uses the **specific Green/convolution form** of the elliptic resolver, or an equivalent resolvent-continuity theorem. It is not a consequence of monotonicity alone. Prove it by dominated convergence against the integrable Green kernel and its derivative.

After these are in place, the rest is formal algebra: pass the stationary equation to the end limit, get the logistic root equation, use the positive lower pin to select the positive root, and squeeze the monotone function between equal end limits to prove `W` is constant.

---

## Global assumptions and notation

The stationary profile satisfies

```text
W'' + c * W' - lambda * W + R(W, V[W]) = 0
```

with `c > 0`, `lambda > 0`. The trap gives:

```text
Antitone W
C2 W
forall x, 0 < c1 <= W x <= C2
bounded W''
```

The normalized positive equilibrium is `Uminus = 1`, so the limiting reaction root is

```text
L * (1 - L^alpha) = 0
```

or, in unnormalized parameters,

```text
L * (a - b * L^alpha) = 0.
```

The proof below uses the normalized form. Replace the final algebraic lemma by the unnormalized one if the Lean parameter structure stores `a,b` explicitly.

---

# A. Derivative vanishing at infinity

## A1. End limits exist

### Lemma

```lean
lemma antitone_bdd_has_limits_atTop_atBot
    {W : R -> R} {c1 C2 : R}
    (hanti : Antitone W)
    (hlb : forall x, c1 <= W x)
    (hub : forall x, W x <= C2) :
    exists Lp Lm,
      Tendsto W atTop (nhds Lp) /\
      Tendsto W atBot (nhds Lm) /\
      c1 <= Lp /\ c1 <= Lm /\ Lp <= Lm
```

For antitone `W`, define

```text
Lp = sInf (Set.range W)
Lm = sSup (Set.range W)
```

Then `W -> Lp` at `atTop` and `W -> Lm` at `atBot`.

### Proof details

For `atTop`, use the infimum characterization. Given `eps > 0`, choose `x0` with `W x0 < Lp + eps`. For `y >= x0`, antitone gives `W y <= W x0 < Lp + eps`, while `Lp <= W y` by the lower-bound property of `sInf`. Hence `|W y - Lp| < eps`.

For `atBot`, either apply the previous argument to `fun x => W (-x)` or use the supremum directly.

### Mathlib pieces

Expected useful names/concepts:

```lean
Antitone
Filter.Tendsto
Filter.atTop
Filter.atBot
sInf
sSup
isGLB
isLUB
Set.range
```

If Mathlib's monotone-convergence lemmas do not fire directly for this exact setup, prove this lemma locally using `sInf`/`sSup` and epsilon arguments.

---

## A2. Bounded `W''` gives uniform continuity of `W'`

### Lemma

```lean
lemma bounded_second_deriv_lipschitz_deriv
    {W : R -> R} {B : R}
    (hC2 : ContDiff R 2 W)
    (hB : forall x, abs (deriv (deriv W) x) <= B)
    (hBnonneg : 0 <= B) :
    LipschitzWith (Real.toNNReal B) (deriv W)
```

A weaker theorem also suffices:

```lean
lemma bounded_second_deriv_uniformContinuous_deriv
    (hC2 : ContDiff R 2 W)
    (hB : exists B, forall x, abs (deriv (deriv W) x) <= B) :
    UniformContinuous (deriv W)
```

### Proof details

By the mean value inequality, if `|(deriv W)'| <= B`, then

```text
|deriv W x - deriv W y| <= B * |x - y|.
```

### Mathlib pieces

Potentially useful:

```lean
Convex.norm_image_sub_le_of_norm_deriv_le_segment
Convex.lipschitzOnWith_of_nnnorm_deriv_le
LipschitzWith.uniformContinuous
```

If these do not match the exact derivative setup on all of `R`, prove the global Lipschitz estimate by applying the one-dimensional mean value theorem on the interval between `x` and `y`.

---

## A3. `W' <= 0` from antitone and differentiability

### Lemma

```lean
lemma deriv_nonpos_of_antitone
    (hanti : Antitone W)
    (hdiff : forall x, DifferentiableAt R W x) :
    forall x, deriv W x <= 0
```

### Proof details

For a differentiable antitone function, the derivative is nonpositive. This follows by applying the derivative definition to nonnegative increments. If Mathlib has a monotone derivative sign lemma, use it; otherwise prove locally.

Possible local proof: for `h > 0`, antitone gives

```text
(W (x+h) - W x) / h <= 0.
```

Pass to the limit as `h -> 0+`.

For the Barbalat contradiction proof below, one may not need this lemma separately if using monotonicity plus interval FTC to produce drops. But it is useful to know that `W'` has a fixed sign.

---

## A4. Barbalat lemma on a half-line

Mathlib does not appear to contain a ready `barbalat` theorem. Prove it locally.

### Version for nonnegative functions

```lean
lemma tendsto_zero_atTop_of_uniformContinuous_nonneg_integrable
    {f : R -> R}
    (hf_uc : UniformContinuous f)
    (hf_nonneg : forall x, 0 <= f x)
    (hf_tail_integrable : exists M, forall A B, A <= B ->
      A >= M -> int x in A..B, f x <= Ctail) :
    Tendsto f atTop (nhds 0)
```

This version encodes finite tail mass in a form usable for monotone profiles. A more standard version is:

```lean
lemma barbalat_atTop
    {f : R -> R}
    (hf_uc : UniformContinuous f)
    (hf_nonneg : forall x, 0 <= f x)
    (hf_integrable : IntegrableOn f (Set.Ioi A)) :
    Tendsto f atTop (nhds 0)
```

### Contradiction proof

Assume not. Then there exists `eps > 0` and a sequence `x_n -> +infty` with

```text
f x_n >= eps.
```

Uniform continuity gives `rho > 0` such that

```text
|y - x_n| < rho -> |f y - f x_n| < eps/2.
```

Hence on `Icc (x_n - rho/2) (x_n + rho/2)`, one has

```text
f y >= eps/2.
```

Choose a subsequence with intervals disjoint and lying in the tail. Then each interval contributes at least

```text
eps * rho / 2
```

of integral mass. Infinitely many disjoint intervals contradict finite tail integrability.

### Easier specialized derivative-drop proof

For the monotone profile, an even simpler proof avoids setting up a full integrability API.

Suppose `W'` does not tend to zero at `+infty`. Since `W' <= 0`, there are `eps > 0` and `x_n -> +infty` with

```text
W' x_n <= -eps.
```

Bounded `W''` gives Lipschitz continuity of `W'`: if `|y - x_n| <= rho`, with

```text
rho = eps / (2*B)
```

then

```text
W' y <= -eps/2.
```

for `B > 0`. If `B = 0`, then `W'` is constant and boundedness forces `W' = 0`.

Taking disjoint intervals `[x_n, x_n + rho]`, the interval FTC gives

```text
W (x_n + rho) <= W x_n - (eps/2) * rho.
```

Infinitely many disjoint intervals force infinitely many fixed drops, contradicting the lower bound on `W`.

This specialized proof is likely the most Lean-friendly.

### Lean lemma shape

```lean
lemma antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atTop
    {W : R -> R}
    (hC2 : ContDiff R 2 W)
    (hanti : Antitone W)
    (hlb : exists m, forall x, m <= W x)
    (hub : exists M, forall x, W x <= M)
    (hWdd_bdd : exists B, 0 <= B /\ forall x, abs (deriv (deriv W) x) <= B) :
    Tendsto (deriv W) atTop (nhds 0)
```

And similarly:

```lean
lemma antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atBot
    ... :
    Tendsto (deriv W) atBot (nhds 0)
```

Use the atTop lemma on `fun x => W (-x)` for atBot.

### Mathlib pieces

```lean
Filter.Tendsto
Filter.atTop
Filter.atBot
UniformContinuous
LipschitzWith
intervalIntegral.integral_eq_sub_of_hasDerivAt
ContDiff
HasDerivAt
```

For disjoint intervals and subsequences, the cleanest implementation is often to avoid explicit subsequences: prove that if for every `X` there exists `x >= X` with `W' x <= -eps`, then recursively construct finitely many disjoint intervals producing `N` drops. For arbitrary `N`, choose `N` large enough to exceed the total bound `C2 - c1`, contradiction.

---

# B. Resolver at a constant end limit

## B1. The statement depends on the resolver form

This step is not a consequence of monotone + bounded + C2. It uses the specific whole-line elliptic resolver.

Assume the chemical equation is

```text
-d2 * V'' + mu * V = nu * W^gamma
```

or, after normalization,

```text
-V'' + mu * V = nu * W^gamma.
```

The whole-line bounded solution is a convolution with an integrable Green kernel. In the normalized case:

```text
G_mu(z) = (1 / (2 * sqrt mu)) * exp(-sqrt mu * |z|)
```

and

```text
V(x) = nu * int_R G_mu(x-y) * W(y)^gamma dy.
```

Also

```text
int_R G_mu = 1 / mu.
```

So the constant source `W = L` gives

```text
V_L = (nu / mu) * L^gamma.
```

For the derivative:

```text
V'(x) = nu * int_R G_mu'(x-y) * W(y)^gamma dy.
```

Since `int_R G_mu' = 0`, rewrite:

```text
V'(x) = nu * int_R G_mu'(z) * (W(x-z)^gamma - L^gamma) dz.
```

Then use dominated convergence.

---

## B2. Resolver convergence theorem

### AtTop

```lean
lemma elliptic_resolver_tendsto_const_atTop
    {W V : R -> R} {L : R}
    (hW_lim : Tendsto W atTop (nhds L))
    (hW_nonneg : forall x, 0 <= W x)
    (hW_bdd : exists M, forall x, W x <= M)
    (hgamma_pos : 0 < gamma)
    (hV_green : forall x,
      V x = nu * int z, Gmu z * (W (x - z))^gamma)
    (hG_int : Integrable Gmu)
    (hG_mass : int z, Gmu z = 1 / mu)
    (hmu : 0 < mu) :
    Tendsto V atTop (nhds ((nu / mu) * L^gamma))
```

### AtBot

Same statement with `atBot`.

### Proof

Write

```text
V x - (nu/mu)*L^gamma
  = nu * int z, Gmu z * (W (x-z)^gamma - L^gamma)
```

For each fixed `z`, as `x -> +infty`, `x - z -> +infty`, hence

```text
W (x-z)^gamma -> L^gamma.
```

Boundedness gives a domination:

```text
|Gmu z * (W (x-z)^gamma - L^gamma)| <= |Gmu z| * C
```

where `C` is a bound for `W^gamma` plus `|L^gamma|`. Since `Gmu` is integrable, dominated convergence applies.

### Mathlib pieces

```lean
MeasureTheory.tendsto_integral_of_dominated_convergence
Integrable
Filter.Tendsto.comp
ContinuousAt.comp
Real.continuousAt_rpow_const
Real.rpow_nonneg
```

The actual rpow continuity is easiest if the lower pin gives `W >= c1 > 0`, so there is no issue with fractional powers. If only `W >= 0`, `rpow` is still continuous on nonnegative arguments for positive exponent, but Lean may require more local lemmas. With the lower pin, the proof is easier.

---

## B3. Resolver derivative convergence

### AtTop

```lean
lemma elliptic_resolver_deriv_tendsto_zero_atTop
    {W V : R -> R} {L : R}
    (hW_lim : Tendsto W atTop (nhds L))
    (hW_nonneg : forall x, 0 <= W x)
    (hW_bdd : exists M, forall x, W x <= M)
    (hgamma_pos : 0 < gamma)
    (hV_deriv_green : forall x,
      deriv V x = nu * int z, GmuDeriv z * (W (x - z))^gamma)
    (hGd_int : Integrable GmuDeriv)
    (hGd_mass_zero : int z, GmuDeriv z = 0) :
    Tendsto (deriv V) atTop (nhds 0)
```

### Proof

Use the zero-mass identity:

```text
V'(x)
= nu * int z, GmuDeriv z * ((W (x-z))^gamma - L^gamma).
```

For each fixed `z`, the bracket tends to zero. Domination is

```text
|GmuDeriv z| * C
```

with `GmuDeriv` integrable. Apply dominated convergence.

### Dependency note

This proof needs the specific Green-kernel representation of the resolver derivative and the fact that the derivative kernel is integrable and has zero integral. If the repository defines the resolver abstractly, first prove a theorem equating it to this Green convolution.

---

## B4. Flux terms vanish

Typical chemotaxis flux terms are built from factors such as

```text
W^m * V'
```

or

```text
W^m * V' / (1 + V)^beta.
```

From

```text
W -> L
V -> V_L
V' -> 0
```

and positivity of the denominator, get:

```lean
lemma chemotaxis_flux_tendsto_zero_atTop
    (hW : Tendsto W atTop (nhds L))
    (hV : Tendsto V atTop (nhds VL))
    (hVp : Tendsto (deriv V) atTop (nhds 0)) :
    Tendsto (fun x => W x^m * deriv V x / (1 + V x)^beta)
      atTop (nhds 0)
```

Use `Tendsto.mul`, `Tendsto.div`, and denominator positivity. With rpow, use continuity on positive arguments.

If the stationary operator contains derivatives of the flux, do not attempt to infer their limit from `flux -> 0`. Instead use the repository's already-expanded stationary equation or prove a dedicated lemma giving the limit of the full source term at a constant state:

```lean
lemma frozen_source_tendsto_constant_state_atTop
    ... :
    Tendsto (fun x => R(W,V) x) atTop
      (nhds (lambda * L - L * (1 - L^alpha)))
```

The exact right-hand side depends on the project's sign convention. This lemma should be the one place that unfolds the chemotaxis formula.

---

# C. Passing the equation to the limit

## C1. Do not assume W'' -> 0 directly

The implication

```text
monotone + bounded + C2 + bounded W''  ==>  W'' -> 0
```

is not valid by itself. The correct route is:

1. The stationary equation expresses `W''` as a function of `W`, `W'`, and resolver terms.
2. Each of those terms has an end limit.
3. Therefore `W''` has a finite end limit `A`.
4. Since `W' -> 0`, this finite limit must be `A = 0`.

## C2. Lemma: if f -> finite and f' -> A, then A = 0

Here `f` will be `W'`.

```lean
lemma tendsto_zero_and_deriv_tendsto_const_forces_const_zero_atTop
    {f fp : R -> R} {A : R}
    (hf : Tendsto f atTop (nhds 0))
    (hfp : Tendsto fp atTop (nhds A))
    (hderiv : forall x, HasDerivAt f (fp x) x) :
    A = 0
```

Proof: if `A > 0`, eventually `fp >= A/2`; by FTC, `f` grows at least linearly on long intervals, contradicting `f -> 0`. If `A < 0`, similarly `f` decreases linearly. Therefore `A=0`.

Mathlib pieces:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt
Filter.Tendsto
Eventually
```

At atBot, apply the atTop version to `fun x => f (-x)` or prove the symmetric lemma.

## C3. Equation limit

From the stationary equation

```text
W'' = -c W' + lambda W - R(W,V)
```

and the limits

```text
W -> L
W' -> 0
R(W,V) -> R_const(L)
```

obtain

```text
W'' -> lambda * L - R_const(L).
```

Then by C2 this limit is zero:

```text
lambda * L - R_const(L) = 0.
```

After simplifying the shifted operator and noting chemotaxis vanishes at constants, get:

```text
L * (1 - L^alpha) = 0.
```

Package this as:

```lean
lemma end_limit_satisfies_logistic_root_atTop
    (hlimW : Tendsto W atTop (nhds L))
    (hlimWp : Tendsto (deriv W) atTop (nhds 0))
    (hresolver : resolver_limit_data_atTop W V L)
    (hstat : forall x, frozenWaveOperator p c W W x = 0) :
    L * (1 - L^p.alpha) = 0
```

and similarly for atBot.

---

# D. Root selection and constancy

## D1. Positive logistic root

With the lower pin, `L >= c1 > 0`, so `L != 0`. From

```text
L * (1 - L^alpha) = 0
```

obtain

```text
L^alpha = 1
```

and hence `L = 1` for `alpha > 0` and `L > 0`.

Lean lemma:

```lean
lemma positive_root_one_of_logistic_root
    (halpha : 0 < alpha)
    (hLpos : 0 < L)
    (hroot : L * (1 - L^alpha) = 0) :
    L = 1
```

Use positivity and rpow injectivity on positive reals. If unnormalized:

```lean
lemma positive_logistic_root_unique
    (ha : 0 < a) (hb : 0 < b) (halpha : 0 < alpha)
    (hLpos : 0 < L)
    (hroot : L * (a - b * L^alpha) = 0) :
    L = (a / b)^(1 / alpha)
```

## D2. Equal end limits force monotone function constant

```lean
lemma antitone_eq_const_of_equal_end_limits
    (hanti : Antitone W)
    (hTop : Tendsto W atTop (nhds L))
    (hBot : Tendsto W atBot (nhds L)) :
    forall x, W x = L
```

Proof: for fixed `x`, antitone gives values to the right `<= W x` and values to the left `>= W x`. Passing to the atTop and atBot limits gives

```text
L <= W x <= L.
```

---

# E. Final theorem chain

Recommended final theorem:

```lean
theorem monotone_stationary_root_pinning_constant
    (htrap : InMonotoneWaveTrapSet ... W)
    (hlower : forall x, c1 <= W x)
    (hc1 : 0 < c1)
    (hC2 : ContDiff R 2 W)
    (hWdd_bdd : exists B, 0 <= B /\ forall x,
      abs (deriv (deriv W) x) <= B)
    (hstat : forall x, frozenWaveOperator p c W W x = 0)
    (hresolverGreen : ResolverGreenRepresentation p W V)
    (hparams : parameter_positivity p) :
    forall x, W x = 1
```

Internal proof:

1. `antitone_bdd_has_limits_atTop_atBot` gives limits `L_plus`, `L_minus`.
2. `antitone_bdd_bounded_second_deriv_deriv_tendsto_zero_atTop` gives `W' -> 0` at `+infty`.
3. Same at `-infty`.
4. `elliptic_resolver_tendsto_const_atTop` and `elliptic_resolver_deriv_tendsto_zero_atTop` give resolver limits.
5. Same at `-infty`.
6. `end_limit_satisfies_logistic_root_atTop` gives `L_plus * (1 - L_plus^alpha)=0`.
7. Same at `-infty`.
8. Lower pin gives both limits positive.
9. `positive_root_one_of_logistic_root` gives `L_plus = 1` and `L_minus = 1`.
10. `antitone_eq_const_of_equal_end_limits` gives `W x = 1` for every `x`.

---

# F. What requires more than monotone + bounded + C2 + bounded W''?

The derivative-vanishing lemma needs only monotone, bounded, C1 plus uniformly continuous derivative. Bounded W'' is a sufficient way to get uniform continuity of W'.

The following steps need extra PDE/resolver structure:

1. `V[W] -> V[L]` and `V'[W] -> 0`. This needs the specific whole-line elliptic resolver representation or an equivalent theorem.
2. Chemotaxis terms vanish at constants. This needs the exact formula of the chemotaxis source.
3. The stationary equation reduces to the logistic root. This needs the exact algebra of `frozenWaveOperator` and the lambda-shift convention.
4. The positive root is `1`. This needs normalized parameters or a separate unnormalized root lemma.

The main false shortcut to avoid is claiming that bounded monotone C2 with bounded W'' automatically gives W'' -> 0. It does not. Instead, first get a finite W'' limit from the stationary equation and resolver convergence, then prove that finite limit is zero because W' -> 0.
