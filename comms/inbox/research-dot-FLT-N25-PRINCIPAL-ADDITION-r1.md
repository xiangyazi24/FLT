# The actual principal divisor satisfies the addition minimum inequality

TASK_ID: FLT-N25-PRINCIPAL-ADDITION
REVISION: 1
TYPE: RESULT
STATUS: GENUINE-LINEAR-SYSTEM-ADDITION-INPUT-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULT: 06f02da731842a497c13bf2d4a5b4189b8bea3e9
SUPERSEDES: none; next concrete linear-system prerequisite

The actual theorem projectivePrincipalDivisor_add_ge_min says that for units
f,g,h in the fixed W-chart function field with value(h)=value(f)+value(g),
every full closed-point coefficient satisfies

    min (projectivePrincipalDivisor f A) (projectivePrincipalDivisor g A) <=
      projectivePrincipalDivisor h A.

The nonzero-sum condition is encoded by h being a unit; zero sums will be
handled separately in the bounded-pole vector-space construction. No valuation
inequality or principal-coefficient compatibility is assumed by the actual
statement. Every boundary and every nonboundary residue degree is included.

## Three modules, eight public declarations

N25F_PrincipalOrderAddition.lean proves the signed DVR-order minimum inequality,
identifies the existing fractional-ideal count with the genuine localization
order for every nonzero fraction, and deduces the same minimum inequality for
the affine fractional-ideal coefficient. The comparison uses the actual
numerator/denominator factor counts, not a renamed valuation.

N25F_ProjectivePrincipalCoefficients.lean reads the X, YZ, Z and nonboundary
coefficients of the existing projective principal divisor from its accepted
split equivalence. It preserves the actual atom indexing and divisor.

N25F_ProjectivePrincipalAddition.lean combines the three coordinate-rigid DVR
orders with the affine count inequality by the accepted exhaustive atom
partition. It supplies the displayed pointwise inequality on the full grading.

## Validation ledger

PASS: generic-02, exact three generic production declarations with unchanged
dependency bodies, exit 0, 19.729 seconds wrapper elapsed, peak RSS
2,928,708 KiB. All three audits standard-three, no warnings/sorryAx.
SHA-256: ec153e8d4b508c3d583b951581ba7b029152f4a62609fb302e9e8768a8004bfa.

PASS: coefficient-02, four complete Finsupp/split-equivalence extraction
checks, exit 0, 18.932 seconds, peak RSS 1,722,712 KiB, all standard-three.
SHA-256: 624b842caa846c02160406ed156c0b444b28fb351acda923ba143cf5d9995d3f.

PASS: addition-family-01, a genuine Dedekind affine principal divisor plus
three DVR orders and an arbitrary exact full-atom partition, exit 0,
54.859 seconds, peak RSS 2,922,116 KiB. The final addition theorem and three
generic dependencies all audit exactly [propext, Classical.choice, Quot.sound].
There are no warnings or sorryAx. This family proves the inequality from
actual fractional-ideal/DVR data; it does not take that inequality as an input.
SHA-256: f8c676976a77cd4aec32b1eff9fcbca5a6b0bbcec7a6a8048687584583dede4b.

The earlier generic-01 and coefficient-01 failures were ordinary API/coercion
errors; their receipts/logs are separated from PASS evidence. Final checked
sources still match their recorded hashes. No successful check was repeated.

The current CurveDedekindDivisor and PrincipalDivisorCoefficient source bytes
match the tested inputs. ProjectiveDivisorSplit has identical declarations
after trailing-whitespace normalization; byte equality is not claimed for it.
Exact blob identities and the source comparison are attached.

NOT RUN locally: the three full named FLT imports and eight production audits.
ActualPrincipalAdditionCheck.lean lists that gate. The families validate the
proofs and indexing mechanism; full named bindings remain pending with the
lead. The declared dependency supplies LocalFractionFactorOrder and its
earlier bounded dependencies. This result does not need the product formula.

Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation, one CPU/thread, 3,072 MiB cap and 60 active compiler seconds.
Wrapper elapsed times may include gate waiting. No broad build.

Next is the actual bounded-pole submodule on the full divisor carrier, using
this addition theorem, and negative-degree vanishing using the delivered
product formula. Finite Picard, the complete-linear-system fibre formula and
the genuine Riemann--Roch identity remain open. No root custom-axiom removal
or fresh full-project acceptance is inferred.

Manifest: comms/inbox/research-dot-FLT-N25-PRINCIPAL-ADDITION-r1-manifest.json
