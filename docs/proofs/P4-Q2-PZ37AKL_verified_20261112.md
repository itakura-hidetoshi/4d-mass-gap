# P4-Q2-PZ37AKL — original Wilson H-uniform top-orthogonal coercivity

Verified 2026-11-12 JST against the exact source, actual PR test merge and
formal squash below. Exact-source and independent formal-push workflows,
full actual logs and separate completion receipts are completed/SUCCESS.

## Exact mathematical scope

Let `P_(H,beta)` be the unchanged genuine SU(2) Wilson physical one-slab
transfer on the original gauge-invariant Haar L2 carrier. Set

\[
S_{H,\beta}=\|P_{H,\beta}\|^{-1}P_{H,\beta},\qquad
K_{H,\beta}=\ker(S_{H,\beta}-I)^\perp.
\]

The full eigenspace is used. No identification of separately selected top
vectors, no top-simplicity premise, and no replacement physical carrier enter.

Define `beta_*` as the canonical
`twoSidedTwelveSpatialUniformGapCutoff 9 (by norm_num)`. The existing theorem
proves `beta_*>0`; the definition has no H argument. AKL proves, for every
`0<=beta<=beta_*`, every `H:Nat`, and every `x` in `K_(H,beta)`:

\[
\|S_{H,\beta}x\|\le\frac{3071}{3072}\|x\|,
\qquad
\boxed{\frac1{3072}\|x\|^2
\le\langle x-S_{H,\beta}x,x\rangle},
\]
\[
\frac1{3072}\|x\|\le\|x-S_{H,\beta}x\|,
\qquad
\frac{6143}{9437184}\|x\|^2
\le\|x\|^2-\|S_{H,\beta}x\|^2.
\]

The raw statement retains the original transfer scale:

\[
\frac{6143}{9437184}\|P_{H,\beta}\|^2\|x\|^2
\le\|P_{H,\beta}\|^2\|x\|^2-\|P_{H,\beta}x\|^2.
\]

The leaf explicitly proves the quantifier order
`exists cutoff>0, forall beta in (0,cutoff], forall H, forall x in K`.
It also chooses `beta=beta_*/2>0` BEFORE quantifying over H. Thus one fixed
positive coupling and one coefficient work for every H. The result is not
obtained by selecting a shrinking volume-dependent coupling.

## Proof and existing provenance

The physical contraction is an existing canonical result in
`PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferUniformTopOrthogonalPowerDecay.lean`,
from the two-sided twelve-spatial uniform gap. The gap coefficient is already
`1/3072`; AKL supplies an explicit quadratic/norm coercivity corollary and a
kernel-checked replay that removes the inherited compiled-decision dependency
described below. It is not presented as a new derivation of the entire physical
high-temperature estimate.

For `q=3071/3072`, Cauchy--Schwarz and the genuine restricted norm bound give

\[
\langle x-Sx,x\rangle
=\|x\|^2-\langle Sx,x\rangle
\ge\|x\|^2-\|Sx\|\|x\|
\ge(1-q)\|x\|^2.
\]

The norm lower bound follows by another Cauchy--Schwarz estimate and division
by `||x||` only when it is positive. Squaring the contraction gives
`1-q^2=6143/9437184`. The existing exact raw/normalized transport gives the
raw defect; its factor `||P||^2` is never canceled out of the asserted floor.

The inherited physical estimate uses actual Haar-to-vacuum and right-boundary
isometries, which send the genuine nonnegative top vector to joint constant
one. Full-top orthogonality therefore removes the intrinsic constant
projection while preserving the physical norm. The final inherited theorem
does not take a uniform Poincare or coercivity estimate as an extra premise.

## Relation to the original source and scope correction

Earlier blanket descriptions of H-uniform coercivity as OPEN are retained
as historical text. The present statement closes the explicitly stated
normalized full-top-orthogonal coercivity on the common positive small-beta
interval, with the fresh certification recorded below.

The original Haar-centered source `f0` is not assumed to lie in this sector.
At positive coupling, AKI/AKK establish a nonzero full-top component. Decomposing
`f0=Qf0+(I-Q)f0` leaves the top component unchanged and contracts only the
orthogonal component. Hence AKK's positive all-power floor and the AJA
non-witness intervals remain compatible with this coercivity theorem.

The following are not established by AKL:

- AKL makes no coercivity claim at the original numerical
  `beta0=log(3/2)/64`, and no claim for all positive couplings.
- An H-uniform original GL posterior-source Rayleigh lower bound.
  The existing comparison from GL mass to posterior energy goes in the
  direction that does not allow an energy lower bound to imply a GL lower bound.
- Positive coercivity on the entire physical space, where `I-S` annihilates
  the top eigenspace, or a positive unscaled raw transfer floor.
- A common-carrier strong-limit construction, a Hamiltonian gap conclusion,
  or a continuum 4D Yang--Mills mass-gap theorem.

## Inherited proof repair

Initial [CI #43165720997](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43165720997)
failed at source `b8e779dede73e6cdab3acb079c7783ab83973330`. The new leaf had two
elaboration errors: physical-subtype normed-space synthesis and an insufficiently
instantiated real-inner rewrite. Full multiline axiom output also exposed
the inherited dependency
`periodicHypercubicEvenGroundStateSpatialColor_card._native.native_decide.ax_1_1`.
That failed run is not certification, and its propagated error placeholders
are not accepted proof terms.

The revised leaf proves the same original six-color cardinality proposition
using `Fintype.card_prod`, the existing kernel-proved `OtherAxis` cardinality,
and ordinary `decide`. It then selectively expands affected theorem and
definition bodies and substitutes that same-type cardinality proof. This also
repairs the proof dependency inside the original finite indexing equivalence.
No imported declaration, physical definition, or assumption is modified.

The proof-construction tactic checks replacement-type equality, rejects
unaccounted dependencies, requires the unchanged target and output to use only
the standard three axioms, checks output-type equality, and explicitly calls
Lean's kernel checker. The resulting theorem is also subject to normal
declaration checking and final `#print axioms`. The tactic implementation is
not a mathematical axiom or a substitute for those checks.

The second attempt, source `1cc720623ab1f68694d433a1987bf2c178720732` and
[CI #43167599956](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43167599956),
also completed FAILURE. The explicit kernel check encountered unresolved
metavariables, and the concrete subtype norm call could not synthesize its
NormedSpace instance. Changed-leaf warning/error counts were 0/2. The clean
cardinality proof compiled with only the standard three axioms; in total 3/11
new mathematical declarations had standard-only audits, while the other 8
contained error-propagated `sorryAx`. Its independent receipt reported
`source_result=failure`, `state=failure`. No certification is drawn from that run.

The third source instantiates both the proof expression and the local context
before the same explicit `Lean.Kernel.check`, rejecting unresolved variables
in every local type and value. It uses the existing generic restriction norm
lemma at power one to avoid reconstructing the concrete subtype's normed-space
instance. This repair changes neither the theorem statements nor their
assumptions, cutoff, physical objects or imported declarations.

Audit counts distinguish the **11 mathematical declarations** (10 theorems and
one cutoff definition) from three private metaprogram helper definitions and
one tactic registration, which can create additional internal names.

## Formal declarations

The [exact new leaf](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/fdd04d5c4655f986e4497dd43701a9edc873909a/MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL.lean)
contains the following mathematical declarations in namespace
`MGAP4D.MathlibAnalytic`, all with prefix `p4Q2PZ37AKL_`.

| Suffix | Role |
|---|---|
| `spatialColor_card_kernel` | Same original finite cardinality, kernel proof |
| `originalUniformCoercivityCutoff` | H-independent cutoff definition at s=9 |
| `originalUniformCoercivityCutoff_pos` | Strict positivity of that cutoff |
| `originalTopOrthogonal_norm_le` | Replayed genuine restricted operator norm |
| `originalTopOrthogonal_apply_norm_le` | Pointwise contraction on the physical carrier |
| `originalTopOrthogonal_quadraticCoercivity` | Quadratic coercivity of I-S |
| `originalTopOrthogonal_normCoercivity` | Norm coercivity of I-S |
| `originalTopOrthogonal_squaredDefect` | Exact dimensionless squared defect |
| `originalTopOrthogonal_rawSquaredDefect` | Raw defect retaining the top scale |
| `exists_positiveUniformCoercivityInterval` | One positive interval before all H |
| `exists_fixedPositiveCoupling_uniformCoercivity` | One fixed positive coupling before all H |

## Exact source and integration

| Item | Value |
|---|---|
| Repository | itakura-hidetoshi/4d-mass-gap |
| Canonical branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Theorem PR | [#6683](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6683) |
| Base | 4b08434ce88d02e897ce1a6f38a5c7515a351a2e |
| Source | fdd04d5c4655f986e4497dd43701a9edc873909a |
| Test merge | 3a2e64550d114524b32b2ddeb0e5d874bfa0acdd |
| Source/test-merge/squash tree | c047dc43f8ec69266add2cd78968e90715c90904 |
| New leaf blob | 563bae143c9bf623c600003a446b6549c059137d |
| Formal squash | 5da8d0ee95089f7a28d15783f483f220f8501327 |
| Lean | v4.30.0-rc2 |
| mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

One new Lean leaf, 327 added lines and zero deletions. No existing Lean,
physical definition, assumption, root import, or pin changes.

## Machine audit

Third exact-source [CI #43169160435](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43169160435): **completed/SUCCESS**.
Build job `131017981581` completed successfully, including Lean step 17,
diagnostic upload, project post-cache and cleanup. The full actual build log
reports **9443/9443**, with the new leaf built in 33 s. All 11 new mathematical
declarations and the separate existing cutoff-positivity audit print exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` remains; changed AKL
warning/error is **0/0**. The 303 warning occurrences in unchanged imported
sources are recorded separately; no Lean error diagnostic occurred.

Independent receipt job `131019776082` completed/SUCCESS and records
`exact_sha=fdd04d5c4655f986e4497dd43701a9edc873909a`,
`source_result=success`, `state=success`, attempt 1. Both exact-source check
runs and the separate commit receipt status are successful. The actual PR
checkout was the test-merge listed above, whose tree equals the source and
formal squash trees. A separate source/log audit reproduced these results.

Independent formal-push [CI #43169855373](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43169855373):
**completed/SUCCESS**, event `push`, exact squash
`5da8d0ee95089f7a28d15783f483f220f8501327`. The actual checkout log identifies
that same commit. Build job `131020285204`, Lean step 17, diagnostic upload,
trusted-branch post-cache step 22 and cleanup completed successfully. The full
actual log again reports **9443/9443**, with the leaf built in 45 s. All 11 new
mathematical declarations and the existing cutoff-positivity audit print
exactly the standard three axioms. Changed AKL warning/error is **0/0**;
`sorryAx` is absent. The 303 existing imported-source warnings are preserved
separately; the log contains no Lean error diagnostic.

Independent receipt job `131022185894` completed/SUCCESS and records
`event=push`, `exact_sha=5da8d0ee95089f7a28d15783f483f220f8501327`,
`source_result=success`, `state=success`, attempt 1. The exact-squash check runs
and separate commit receipt status are successful. A separate log/identity
audit reproduced these results.

| Gate | Exact-source PR run | Independent formal push |
|---|---|---|
| Workflow | 43169160435 SUCCESS | 43169855373 SUCCESS |
| Build job | 131017981581 SUCCESS | 131020285204 SUCCESS |
| Lean dependency closure | 9443/9443 | 9443/9443 |
| New mathematical audits | 11/11 standard three only | 11/11 standard three only |
| Existing cutoff-positivity audit | Standard three only | Standard three only |
| Changed AKL warning/error | 0/0 | 0/0 |
| New sorryAx / native dependency | Absent | Absent |
| Imported-source warning occurrences | 303 | 303 |
| Completion receipt job | 131019776082 SUCCESS | 131022185894 SUCCESS |

The eleven new mathematical declarations each have an explicit axiom audit.
The existing clean cutoff-positivity theorem receives one additional audit.
These are complete multiline-array audits, including every continuation line.
The dependency-closure count is for this leaf and its imports; it is not copied
from AKK's different import closure. The receipt is checked alongside the
actual build log and does not replace kernel verification. The old native-card
declaration itself remains unchanged; its dependency is absent from the new
mathematical declarations.

## Publication rule

Formal receives the proof leaf and the append-only proof record. Main receives
the identical proof-record Git blob and identical README/ROADMAP appendices,
with no formal-only Lean leaf copied. append-only / tighten-only /
overwrite-forbidden / same-root remain in force.
