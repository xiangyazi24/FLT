# Q3184 (dm2): Paper 2 Round 10 — Paper Architecture and Chan Connection

Date: 2026-07-03

## Executive recommendation

For a 10-page DNA conference paper, the strongest framing is:

```text
Start from Chan's Theta_10 and the factorization question directly;
then explain that the obstruction is a surviving mock modular slab.
```

Use the broader real-quadratic context only as the opening motivation, and use the computational observation only as the discovery story. The paper should not read like a long computational postmortem. It should read like a precise theorem about the first place where a natural theta-product factorization mechanism breaks.

The main message should be:

```text
Chan's n = 10 dissection almost factors. The interior cancels by a clean involution,
but the boundary/slab that remains is a genuine indefinite theta object with
nonzero Zwegers shadow. Therefore the obstruction to theta-product factorization
is not noise; it is mock modularity.
```

This turns the negative result into a positive structural theorem.

---

## Q1. Paper introduction

### Recommended opening strategy

Use option **(a)** as the spine:

```text
Begin with Chan's Theta_10 and the product-factorization question.
```

But do not make the first paragraph too narrow. The best 10-page introduction has this order:

1. **General context, one paragraph only.**  Real quadratic theta series often have product expansions or decompositions into unary theta factors after a suitable dissection. This is the conceptual background.
2. **Chan hook.**  Chan's rank-10 theta function is a concrete and natural test case in this program.
3. **Question.**  Does `Theta_10` factor as a product of weight-1/2 theta functions?
4. **Answer.**  No. The obstruction is a mock modular correction supported on a finite slab.
5. **Method.**  Sigma involution cancels the interior; the residual slab is put into Pell coordinates; Zwegers theory proves a nonzero shadow.

### Why not start with the computation?

The `430/450 success` observation is useful, but it should not be the first thing the reader sees. It sounds provisional. The theorems are stronger than the computation.

Use the computation in the introduction as a short diagnostic sentence, for example:

```text
A finite-fiber pairing succeeds in all ordinary fibers and fails only on a thin
family of boundary fibers. This numerical anomaly led us to the missing slab.
```

Then immediately state that the anomaly is now explained by Theorems 1--4.

### Suggested 10-page architecture

A good page budget is:

| Section | Pages | Purpose |
|---|---:|---|
| 1. Introduction and main theorem | 1.0--1.25 | State Chan question, answer, and obstruction |
| 2. Chan's `Theta_10` dissection | 1.0--1.5 | Define `K`, `L`, coordinates, signs, exponent separation |
| 3. Sigma cancellation and slab decomposition | 2.0 | Prove Theorems 1 and 2 |
| 4. Pell coordinates and unit dynamics | 1.5 | Prove Theorem 3 |
| 5. Zwegers completion and nonzero shadow | 2.0 | Prove Theorem 4 |
| 6. Consequences, evidence table, and outlook | 1.0 | Explain factorization failure, include compact tables |

The introduction should advertise the four theorems as one pipeline:

```text
Chan dissection -> sigma cancellation -> slab residual -> Pell form -> Zwegers mock modularity -> no theta-product factorization.
```

---

## Q2. The precise factorization statement

### Q2a. Is this the right way to state the failure?

Yes, with one wording correction.

The correction term does factor in the weak algebraic sense

```text
Correction = Theta_u * Theta_v * F_slab.
```

But that is not the factorization Chan-style theta-product factorization asks for. The permitted factors are honest weight-1/2 theta functions, hence honest holomorphic modular objects with zero mock shadow. The factor `F_slab` is not an honest theta function. It is the holomorphic part of an indefinite theta completion with nonzero shadow.

So the clean distinction is:

```text
Theta_10 does decompose.
Theta_10 does not factor as a product of classical weight-1/2 theta functions.
```

That distinction should be made explicitly, because otherwise the formula

```text
Correction = Theta_u * Theta_v * F_slab
```

looks like a contradiction to the claim that factorization fails.

### Q2b. Cleaner formulation

Use a theorem like this.

```text
Main Theorem.
In Chan's n = 10 dissection one has

    Theta_10 = Main + Theta_u Theta_v F_slab,

where Main is the term predicted by the theta-product pairing and F_slab is the
holomorphic part of a Zwegers indefinite theta function. The completion of
F_slab has nonzero shadow. Consequently the residual term is genuinely mock,
and Theta_10 cannot be represented by the proposed product of honest weight-1/2
theta functions.
```

An even sharper slogan is:

```text
The obstruction to Chan-style factorization is the nonzero shadow of F_slab.
```

This is probably the sentence that should appear in the abstract.

### Why the nonzero shadow proves non-factorization

The logic is:

1. A product of honest weight-1/2 theta functions is an honest modular object; its completion has zero mock shadow.
2. The main term is honest/modular in the relevant sense.
3. `F_slab` has a Zwegers completion with nonzero shadow.
4. Multiplying by the honest theta prefactor `Theta_u Theta_v` does not make that shadow vanish.
5. Therefore the residual is not a product of honest theta factors.

The key technical phrase is:

```text
nonzero shadow is incompatible with a pure theta-product identity.
```

A cautious version, if one wants to avoid quotient issues at zeros, is:

```text
The holomorphic q-series produced by the n = 10 dissection has a nontrivial
mock component. Hence it is not generated solely by the classical theta factors
appearing in the proposed factorization.
```

---

## Q3. Relation to Chan's work

### Q3a. What does Chan prove for `n = 10`?

From the information in the prompt alone, I would **not** claim that Chan proves a false factorization for `n = 10`. The paper should be careful here.

Recommended neutral wording:

```text
Chan's dissection framework naturally suggests a theta-product factorization in
several cases. We analyze the n = 10 case and show that the expected pairing is
not complete: after the interior cancellation, a slab residual remains. This
residual is mock modular and is the precise obstruction to a pure theta-product
formula.
```

If Chan explicitly states an `n = 10` product identity, then your result is a correction/counterexample to that statement. If Chan instead leaves `n = 10` as problematic or treats it by a more complicated residual identity, then your result is the structural explanation of the problematic term.

For the conference paper, avoid phrasing like:

```text
Chan is wrong.
```

Use:

```text
The n = 10 case contains an additional mock modular correction term not captured
by the naive theta-product pairing.
```

That is mathematically stronger and less adversarial.

### Q3b. For which `n` does factorization work, and why does `n = 10` fail?

The safe criterion is structural, not a list of `n` values.

Factorization works in the cases where the dissection support is fully paired by the available sign-reversing involutions, including all boundary pieces. Equivalently:

```text
residual slab empty or shadow zero  =>  theta-product factorization can survive;
residual slab nonempty with nonparallel negative cusp vectors  =>  mock obstruction.
```

In the `n = 10` case, the interior of Half B cancels by

```text
sigma_k(r) = -(6k+1) - r,
```

but the slab survives. In Pell coordinates the inner form becomes

```text
Q_form = x^2 - 5 y^2,
```

with automorph eigenvalue

```text
epsilon^6 = 9 + 4 sqrt(5).
```

The two cusp vectors

```text
c_1 = (-1, 3),
c_2 = (-3, 14)
```

are both negative and nonparallel, with

```text
det(c_1, c_2) = -5.
```

That is the geometric reason the residual is a genuine Zwegers indefinite theta object rather than an honest theta product.

So the criterion to state is:

```text
A Chan dissection factors precisely when all signed cone-boundary residuals
cancel or have zero shadow. The n = 10 case fails because its boundary residual
is a nondegenerate indefinite theta slab with nonzero shadow.
```

If the paper includes a table of Chan's other `n` values, classify them by this criterion:

| Case type | Condition | Outcome |
|---|---|---|
| Paired interior and paired boundary | all atoms matched by sign-reversing involutions | theta-product possible |
| Boundary remains but cusp vectors degenerate | shadow zero / reducible correction | theta or false-theta simplification possible |
| Boundary slab with nonparallel negative cusps | nonzero Zwegers shadow | mock obstruction; no pure theta product |

Do not claim a complete all-`n` theorem unless the table has been checked case-by-case.

### Q3c. What is special about discriminant 20?

There are two discriminants in the story:

```text
field discriminant of Q(sqrt(5)): 5;
classical binary-form discriminant of x^2 - 5y^2: 20.
```

The `disc 20` language comes from the Pell form

```text
x^2 - 5y^2,
```

whose classical form discriminant is `0^2 - 4(1)(-5) = 20`.

What makes this case special is not merely that the number 20 appears. The special combination is:

1. The real quadratic field is `Q(sqrt(5))`, the Rogers--Ramanujan/quintic field.
2. The inner form has a nontrivial Pell automorphism with return unit `epsilon^6 = 9 + 4 sqrt(5)`.
3. The support cone has two nonparallel negative boundary vectors.
4. The boundary determinant is `5`, so the slab is genuinely tied to the `sqrt(5)` arithmetic.
5. The wall correction vanishes, so the slab is the first surviving obstruction.

Other discriminants such as 12, 24, 28, and so on may have analogous bad behavior if their dissections leave an indefinite slab with nonzero shadow. The likely general principle is:

```text
bad discriminant = surviving nondegenerate cone-boundary theta with nonzero shadow.
```

The special feature of discriminant 20 is that this phenomenon appears in a small, explicit, Rogers--Ramanujan-adjacent case where the entire obstruction can be written down and proved.

---

## Q4. Numerical evidence tables

For a 10-page paper, include only the tables that clarify the proof. I recommend two main tables and one optional appendix table.

### Main Table 1: cancellation anatomy

This is the most important table. It should show how the support decomposes and where the residual lives.

Suggested columns:

| Region | Involution/action | Contribution |
|---|---|---:|
| Half B interior | `sigma_k` | cancels |
| wall `k = 0` | `r <-> -(r+1)` | cancels |
| Slab+ | none | survives |
| Slab- | none | survives |
| total slab | Zwegers correction | mock |

This table supports Theorems 1 and 2 and helps non-specialists follow the proof.

### Main Table 2: first coefficients of `F_slab`

Include the first 20 or 30 nonzero values of `F_slab`, not just the full `Theta_10` coefficients. The reader needs to see the obstruction itself.

Suggested columns:

| exponent | coefficient of `F_slab` | Slab+ count | Slab- count | net sign |
|---:|---:|---:|---:|---:|

If space is tight, use only:

```text
Q-value, coefficient
```

The coefficient table is most useful if it is visibly not a theta-product coefficient pattern.

### Optional Table 3: finite-fiber diagnostic / failure rates

The `430/450` success statistic is good as a discovery diagnostic, but not as a central theorem table. Include a small table if it illustrates the boundary nature of the failure:

| exponent range | tau-paired fibers | defective fibers | defect condition |
|---:|---:|---:|---|
| sample range | count | count | `9 | e` |

This table should support the sentence:

```text
The finite pairing fails only on the 9-dissection boundary.
```

### Lower priority: multiplicativity table

A table of multiplicativity failures or `chi(p)` values is useful only if the paper also makes a separate claim ruling out eta-products or eigenform-like product formulas. It is not necessary for the main mock-modularity proof.

If included, put it after the main theorem as a short consequence:

```text
The first multiplicativity failures are numerical shadows of the nonzero mock shadow.
```

### Lower priority: raw slab atom counts by `(k,r)` region

These are useful for debugging and for an appendix, but they can be too implementation-specific for a 10-page conference paper. Prefer the conceptual cancellation-anatomy table in the main text.

### Reproducibility helper for tables

If the code base already computes slab coefficients, the paper can use a tiny renderer like this to generate Markdown tables consistently.

```python
from dataclasses import dataclass
from typing import Iterable, List, Sequence


@dataclass(frozen=True)
class SlabCoeff:
    exponent: int
    coefficient: int
    slab_plus_count: int = 0
    slab_minus_count: int = 0


def markdown_table(rows: Sequence[SlabCoeff], limit: int = 30) -> str:
    """Render the first `limit` slab coefficient rows as a Markdown table."""
    header = "| exponent | coefficient | Slab+ count | Slab- count |\n"
    sep = "|---:|---:|---:|---:|\n"
    body_lines: List[str] = []
    for row in rows[:limit]:
        body_lines.append(
            f"| {row.exponent} | {row.coefficient} | "
            f"{row.slab_plus_count} | {row.slab_minus_count} |"
        )
    return header + sep + "\n".join(body_lines)


def nonzero_rows(rows: Iterable[SlabCoeff]) -> List[SlabCoeff]:
    """Keep only nonzero coefficients, preserving order."""
    return [row for row in rows if row.coefficient != 0]
```

---

## Q5. Title and abstract

### Recommended title

```text
A Mock Modular Obstruction to Theta-Product Factorization in Chan's Theta_10
```

Other good options:

```text
The Mock Slab in Chan's Theta_10
```

```text
A Discriminant-20 Counterexample to Theta-Product Factorization
```

```text
When a Real-Quadratic Theta Product Fails: Mock Modularity in Theta_10
```

The first title is the best conference title: it says the object, the claim, and the mechanism.

### 150-word abstract

```text
Chan's q-series dissections suggest that certain real-quadratic theta functions
should factor into products of weight-1/2 theta functions. We analyze the rank-10
case attached to Q(sqrt(5)) and prove that the expected factorization fails for a
structural reason: a surviving boundary slab is mock modular. The exponent
separates into two unary theta variables and an inner discriminant-20 Pell form.
A sign-reversing involution sigma_k cancels the interior contribution, and the
remaining term decomposes as Theta_u Theta_v F_slab. In Pell coordinates the inner
form is x^2 - 5y^2, with automorphism eigenvalue epsilon^6 = 9 + 4 sqrt(5). The
slab is bounded by two negative, nonparallel cusp vectors c_1=(-1,3) and
c_2=(-3,14), so Zwegers' indefinite theta theory gives a completion with nonzero
shadow. Hence F_slab is genuinely mock, and Theta_10 is not a product of honest
weight-1/2 theta functions.
```

This is 150 words if `Theta_10`, `F_slab`, and `Q(sqrt(5))` are counted as one token each in the usual mathematical-word sense; if the conference uses a strict automated word counter, trim the first sentence to:

```text
Chan's dissections suggest that some real-quadratic theta functions factor into products of weight-1/2 theta functions.
```

---

## Q6. What is left open?

Theorems 1--4 are enough for the main conference paper. The future-work section should be short and focused.

### 1. Explicit Appell--Lerch / Hickerson--Mortenson form for `F_slab`

This is the most natural next project. The current theorem proves mock modularity geometrically through Zwegers' completion. An explicit Appell--Lerch formula would make the obstruction more recognizable and may connect it to known Rogers--Ramanujan or quintuple-product expressions.

Future-work sentence:

```text
It remains to express F_slab explicitly as an Appell--Lerch sum plus theta terms,
which should be possible by matching the discriminant-20 slab to the
Hickerson--Mortenson Hecke-type double-sum framework.
```

### 2. Level, character, and Weil representation

The paper should not overclaim the exact scalar level unless it has been computed. The natural completed object is vector-valued. Determining its scalar level and character is a clean follow-up.

Future-work sentence:

```text
A second direction is to compute the precise level, multiplier, and
Weil-representation component of the Zwegers completion.
```

### 3. General bad-discriminant criterion

This is the broadest mathematical continuation. The likely criterion is:

```text
factorization fails exactly when the Chan dissection leaves a nondegenerate
indefinite slab with nonzero shadow.
```

But that should be presented as a conjectural program, not as a theorem, unless the other discriminants have been checked.

Future-work sentence:

```text
The n = 10 case suggests a general criterion for bad discriminants: after all
finite involutions have been applied, a nonempty slab with nonparallel negative
cusps produces a mock obstruction.
```

### 4. The onset artifact: first nonzero total charge at `Q = 14`

This is interesting but probably not central to the 10-page paper. Mention it only in the outlook unless it has a clean theorem.

Possible interpretation:

```text
The onset at Q = 14 appears to measure the first lattice point at which the slab
escapes all wall cancellations. It should be an arithmetic minimum of the shifted
Pell coset subject to the slab inequalities.
```

A future theorem could identify `14` as a constrained minimum:

```text
min { Q_inner(v + mu) : v lies in the surviving slab and has nonzero signed charge }.
```

### 5. Exact relationship to Chan's list of `n`

For the final journal version, include a full table comparing all of Chan's `n` cases:

| `n` | field/form | dissection residual | shadow | outcome |
|---:|---|---|---|---|

This would turn the paper from a single counterexample into a classification program.

### 6. Formal verification / implementation audit

Because Rounds 1--9 include many coordinate changes and involutions, a small formal appendix or machine-checkable notebook would be valuable. The critical identities to audit are:

```text
sigma preserves Q_inner;
sigma flips (-1)^r;
wall correction vanishes;
Q_inner = Q_form(v + mu) - 1/5;
B(v,c_1) = 5k;
B(v,c_2) = 5(6k+r);
det(c_1,c_2) = -5.
```

This is not needed for the conference proof, but it is useful for long-term reliability.

---

## Suggested final theorem block for the paper

Here is a compact statement that can be placed near the end of the introduction.

```text
Theorem.
Let Theta_10 be Chan's rank-10 theta series attached to the coset
L = {a + b phi : b - 3a == 1 mod 10} in Z[phi]. In the n = 10 dissection,
the signed atom contribution decomposes as

    Theta_10 = Main + Theta_u Theta_v F_slab.

The main term is the factorable contribution predicted by the interior pairing.
The slab term F_slab is the holomorphic part of a Zwegers indefinite theta
function attached to the discriminant-20 form x^2 - 5y^2. Its boundary cusp
vectors c_1=(-1,3) and c_2=(-3,14) are negative and nonparallel, and the resulting
shadow is nonzero. Consequently F_slab is genuinely mock modular. In particular,
Theta_10 is not a product of honest weight-1/2 theta functions.
```

This theorem is clean, self-contained, and matches the four established theorems:

```text
Theorem 1: sigma cancellation.
Theorem 2: slab decomposition.
Theorem 3: Pell structure.
Theorem 4: nonzero Zwegers shadow.
```

---

## Final answers to Q1--Q6

1. **Introduction:** use approach (a), with one paragraph of (b) and a brief discovery note from (c). Lead with Chan's `Theta_10` and the factorization question.

2. **Precise failure:** yes, the correction factors as `Theta_u Theta_v F_slab`, but not into allowed theta factors. The obstruction is that `F_slab` has nonzero mock shadow.

3. **Chan connection:** phrase the paper as explaining the `n = 10` obstruction in Chan's framework. Do not claim Chan proved a false identity unless the exact statement is quoted. Factorization works when all boundary residuals cancel or have zero shadow; `n = 10` fails because a discriminant-20 slab survives.

4. **Tables:** include cancellation anatomy and first `F_slab` coefficients. Add finite-fiber failure rates only as a diagnostic. Multiplicativity failures are optional and secondary.

5. **Title/abstract:** best title is `A Mock Modular Obstruction to Theta-Product Factorization in Chan's Theta_10`; the abstract above is ready to use.

6. **Open work:** Appell--Lerch closed form, exact level/character, classification of bad discriminants, explanation of the `Q = 14` onset, and formal/computational audit of the coordinate identities.
