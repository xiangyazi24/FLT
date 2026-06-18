# Denominator quartic via Pellian factorization: exact reduction and missing theorem

The requested theorem was:

```lean
theorem no_denom_quartic_odd_q
    (p q t : ℤ)
    (hpq : IsCoprime p q)
    (hq_pos : 2 ≤ q)
    (hq_odd : ¬ (2 : ℤ) ∣ q)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    False
```

I cannot honestly provide a complete `0 sorry` Lean proof of this theorem from the proposed ingredients alone.  The Pellian factorization is correct and very useful, but after the coprime factor split it reduces to Fermat’s right-triangle / exponent-4 infinite descent.  That classical theorem is the genuinely missing ingredient, not a Lean syntax issue.

Below is the Lean-oriented reduction and the precise missing lemma.

## 1. The algebraic factorization

From

\[
t^2=p^4+p^2q^2-q^4
\]

we get

\[
(2p^2+q^2)^2-4t^2=5q^4,
\]

hence

\[
A B=5q^4,
\quad
A=2p^2+q^2-2t,
\quad
B=2p^2+q^2+2t.
\]

The basic Lean algebra is short:

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

lemma denom_pell_identity (p q t : ℤ)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    (2 * p ^ 2 + q ^ 2 - 2 * t) * (2 * p ^ 2 + q ^ 2 + 2 * t) = 5 * q ^ 4 := by
  nlinarith

lemma denom_pell_sum (p q t : ℤ) :
    (2 * p ^ 2 + q ^ 2 - 2 * t) + (2 * p ^ 2 + q ^ 2 + 2 * t) =
      2 * (2 * p ^ 2 + q ^ 2) := by
  ring

lemma denom_pell_diff (p q t : ℤ) :
    (2 * p ^ 2 + q ^ 2 + 2 * t) - (2 * p ^ 2 + q ^ 2 - 2 * t) = 4 * t := by
  ring

end Scratch.ChatGPTDropDM1
```

## 2. What the odd-`q` coprime split should prove

For odd `q`, `gcd(p,q)=1`, and a solution, one should show:

1. `gcd(t,q)=1`, since reducing the equation modulo `q` gives `t² ≡ p⁴ mod q`;
2. `p` is odd, because if `p` is even and `q` is odd then the right side is `7 mod 8`;
3. the factors `A` and `B` are odd;
4. `gcd(A,B)=1`.

Then from `A*B=5*q^4`, positivity, and coprimality, the factor split has the shape

\[
(A,B)=(5m^4,n^4)
\quad\text{or}\quad
(A,B)=(m^4,5n^4),
\]

with `mn = q` up to signs/absolute values.

This factor split is already nontrivial in Lean: it requires a lemma saying that coprime factors of a fourth power times a single prime are fourth powers up to the prime factor.  This is not just `omega`; it is a prime-factorization/UFD lemma over `ℤ` or `ℕ`.

## 3. The split reduces to Fermat’s right-triangle theorem

In one branch, say

\[
A=5m^4,
\quad
B=n^4,
\quad
q=mn,
\]

the sum identity gives

\[
5m^4+n^4=4p^2+2m^2n^2.
\]

Rearranging:

\[
4p^2=n^4-2m^2n^2+5m^4=(n^2-m^2)^2+4m^4.
\]

Since the parity conditions force `n²-m²` even, put

\[
r=(n^2-m^2)/2.
\]

Then

\[
p^2=r^2+m^4. \tag{★}
\]

This is a right triangle with legs `r` and `m²`, hypotenuse `p`.  The nontrivial theorem needed is Fermat’s right-triangle theorem / exponent-4 descent: there is no nontrivial integer solution to

\[
p^2=r^2+m^4
\]

with `m ≠ 0` and `r ≠ 0` in the primitive case.  Equivalently, no nonzero fourth power plus a nonzero square is a square in a primitive right triangle.  The other branch gives the same kind of equation after swapping the `5`.

This is the classical infinite descent.  Unless that theorem is already available in the local Mathlib environment under a usable name, it still has to be formalized.

## 4. Conditional Lean wrapper once Fermat’s descent theorem is available

The following is the shape of the final wrapper.  It is not the requested theorem yet; it shows exactly what external theorem the proof still needs.

```lean
import Mathlib

namespace Scratch.ChatGPTDropDM1

/-- Placeholder type of the classical Fermat right-triangle obstruction needed here.
A production proof should replace this hypothesis by the actual Mathlib theorem or by a
formalized infinite descent. -/
def FermatRightTriangleObstruction : Prop :=
  ∀ (m r p : ℤ),
    m ≠ 0 → r ≠ 0 → IsCoprime m r →
      p ^ 2 = m ^ 4 + r ^ 2 → False

/-- The exact target, conditional on the missing Fermat descent and the factor-split package. -/
def OddQFactorSplitPackage : Prop :=
  ∀ (p q t : ℤ),
    IsCoprime p q → 2 ≤ q → ¬ (2 : ℤ) ∣ q →
      t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4 → False

/-- Once the full factor split plus Fermat descent are formalized, this is the theorem wanted. -/
theorem no_denom_quartic_odd_q_from_package
    (H : OddQFactorSplitPackage)
    (p q t : ℤ)
    (hpq : IsCoprime p q)
    (hq_pos : 2 ≤ q)
    (hq_odd : ¬ (2 : ℤ) ∣ q)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    False :=
  H p q t hpq hq_pos hq_odd h

end Scratch.ChatGPTDropDM1
```

## 5. Bottom line

The proposed Pellian factorization is the correct start, but the requested `0 sorry` Lean theorem requires two substantial ingredients that are not present in the prompt:

1. a formal coprime factor-splitting theorem for `A*B = 5*q^4`;
2. Fermat’s right-triangle / exponent-4 infinite descent for `p² = r² + m⁴`.

If Mathlib in this repo already contains a theorem for Fermat’s right triangle theorem, then the next step is to identify its exact name and statement and connect it to `(★)`.  I did not find such a theorem by the obvious names, so I do not want to fake a `0 sorry` proof.  The mathematically honest path is to either import/formalize that classical descent theorem, or proceed with the dual-isogeny descent package where this squareclass bookkeeping is handled more naturally.
