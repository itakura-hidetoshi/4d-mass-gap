# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-14 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest mathematical theorem baseline before this documentation refresh is

```text
1696ba98d930c5f59293319fc562d057d4b7586e
```

which is the normal merge of PR #4080,

```text
Factor C5 reference fiber through one-slab raw Doob law
```

with exact GREEN theorem head and validation

```text
head:
  154c124671170bdf3975c7e3d1aeb351d9dda026

PR Lean Fast Check #13798
workflow run 34787609915
completed / success
```

A documentation-only merge may advance the authoritative branch pointer without changing this mathematical theorem baseline. `main` is a public landing surface. Only theorem results merged into the authoritative theorem carrier count as canonical proof status.

> **Current frontier**
>
> The full normalized reference-law one-link conditional-specification ladder is now integrated: exact Fubini compatibility, measurable heat-bath kernel, stationarity, idempotence, off-fiber factorization, properness, setwise and integral conditional identities, conditional expectation, RCD identification, and conditional-variance transport are all canonical through PR #4077.
>
> PR #4080 then exposes the C5 reference fiber as a continuous-vacuum Doob tilt of a normalized one-slab `local × kernel` raw law, without identifying that raw law with the full-4D Wilson `singleLinkConditionalMeasure`.
>
> The immediate open problem is quantitative rather than measure-theoretic: prove a distance-sensitive or otherwise summable remote conditional-law / covariance estimate that overcomes the link-count obstruction of #3969 and yields volume-independent same-color block coercivity.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated on bounded core** — canonical on the explicit dense bounded concrete core; no arbitrary-`L²` pointwise statement is implied.
- **Integrated routing** — implication chain is formalized, but a model-derived quantitative input is still missing.
- **Obstruction integrated** — a rigorous negative result rules out a tempting route.
- **Open now** — immediate constructive frontier.
- **Open next** — next coherent unit after the current frontier.
- **Open downstream** — required later in the global gap route.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                         [Integrated]
  -> reflection positivity / boundary geometry                       [Integrated]
  -> physical one-slab transfer                                      [Integrated]
  -> positive / strictly-positive ground-state transfer geometry     [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> continuum scalar law                                            [Integrated]
  -> continuum OS positivity                                         [Integrated]
  -> Hilbert carrier / real C0 semigroup / self-adjoint Hamiltonian  [Integrated]
  -> vacuum Omega / complete Omega-perp                              [Integrated]

C. FINITE GROUND-STATE CONDITIONAL DYNAMICS

ground-state one-slab joint probability law                          [Integrated]
  -> 6 right + 6 left genuine spatial condExp projections            [Integrated]
  -> genuine 12-spatial family                                      [Integrated]
  -> E12 -> E6 -> raw physical defect -> transfer gap                [Integrated routing]

D. SHARP ONE-LINK CONTROL

complete continuous-vacuum one-link weight                           [#3894]
  -> sharp normalized Haar comparison                               [#3898]
  -> exp(-16 beta) one-link variance lower bound                     [#3907]
  -> a.e. actual joint split-fiber compatibility                     [#3909]
  -> genuine joint condExpL2 residual on bounded core                [#3921-#3952]
                                                                     [Integrated]

E. REMOTE-INFLUENCE OBSTRUCTION

single-source remote weight / Doob comparison                        [#3954, #3959]
  -> bounded-test influence                                          [#3964]
  -> naive row majorant carries remote-link cardinality              [#3969]
                                                                     [Obstruction integrated]

F. LOCALITY AND COVARIANCE LOCALIZATION

raw same-color Wilson cancellation                                   [#3978]
  -> source likelihood ratio is source-link local                    [#3991, #3994]
  -> physical four-point defect = weighted covariance                [#3997, #4000]
  -> target-local x source-local covariance                          [#4004]
  -> canonical positive continuous-vacuum reference weight           [#4011]
  -> normalized reference probability law                           [#4016]
                                                                     [Integrated]

G. REFERENCE ONE-LINK DISINTEGRATION / RCD

literal normalized fiber law                                         [#4019]
  -> singleton marginal / normalized density                         [#4024, #4027]
  -> local normalization identity                                    [#4030]
  -> full-law Fubini compatibility                                   [#4035]
  -> measurable heat-bath kernel + stationarity                      [#4039]
  -> idempotence                                                      [#4042]
  -> off-fiber sigma algebra factorization                           [#4045]
  -> proper off-fiber kernel                                         [#4048]
  -> setwise conditional identity                                    [#4054]
  -> nonnegative / real conditional integral identities              [#4057, #4060]
  -> conditional expectation                                         [#4066]
  -> RCD / condExpKernel identification                              [#4070]
  -> conditional variance transport                                  [#4077]
                                                                     [Integrated]

H. C5 RAW-DOOB FACTORIZATION

q_A = local x one-slab kernel                                        [#4080]
  -> normalized raw law nu_A                                         [Integrated]
  -> reference fiber weight = Omega_cont x q_A                      [Integrated]
  -> normalized Doob composition                                     [Integrated]
  -> C5 fiber = Doob_{Omega_cont}(nu_A)                              [Integrated]

I. SUMMABLE REMOTE MIXING

actual reference RCD + C5 raw-Doob factorization
  -> quantitative remote conditional-law comparison                  [OPEN NOW]
  -> distance-sensitive / summable covariance or influence          [OPEN NOW]
  -> volume-independent same-color row bound                         [OPEN NEXT]
  -> one color-block coercivity                                      [OPEN NEXT]

J. GLOBAL FINITE-VOLUME COERCIVITY

six right + six left color/block estimates                           [OPEN]
  -> quantitative E12 Poincare coefficient                          [OPEN]
  -> model-derived kappa(H,N,beta) > 0                              [OPEN]
  -> scale-independent kappa_* > 0                                  [OPEN]
  -> physical transfer gap >= 3 kappa_*/4                           [Integrated routing]

K. THERMODYNAMIC / CONTINUUM PROPAGATION

uniform finite-volume physical transfer gap                          [OPEN DOWNSTREAM]
  -> stable Green / resolvent / Poincare control                     [OPEN DOWNSTREAM]
  -> thermodynamic / scaling-limit physical carrier                  [OPEN DOWNSTREAM]
  -> physical OS/Wightman spectral lower bound                       [OPEN DOWNSTREAM]

L. CLAY-LEVEL COMPLETION

sufficiently rich same-root 4D continuum Yang--Mills field/state     [OPEN]
correct vacuum structure / nontriviality                             [OPEN]
physical OS/Wightman identification                                  [OPEN]
strict positive spectrum above the vacuum sector                     [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules:

```text
start from the exact authoritative canonical SHA
use GitHub-mediated repository operations
accept CI only when workflow / job / Lean step are terminal success
keep write-freeze while exact-head CI is active
inspect the first genuine terminal Lean failure before editing
keep theorem development additive / tighten-only
never strengthen assumptions merely to make elaboration easier
forbid sorry / admit / new axiom / proof placeholders
merge with expected head SHA fixed
re-observe the canonical branch after merge
```

Permanent claim boundaries:

```text
finite theorem != continuum theorem
positive coefficient at each scale != uniform positive coefficient
local Harnack / Doeblin / variance != global L2 Poincare
bounded-core theorem != arbitrary-L2 pointwise theorem
raw Wilson K = 1 != continuous-vacuum Doob K = 1
covariance localization != covariance decay
RCD identification != quantitative mixing
one-link RCD != full-Wilson singleLinkConditionalMeasure
C5 raw law != full-4D Wilson single-link conditional law
uniform pairwise remote bound != summable row bound
same-root scalar continuum != full 4D Yang--Mills field
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root contains the interacting periodic-even compact special-unitary Wilson Gibbs model, normalized compact Haar reference measure, lattice/plaquette geometry, Wilson action, reflection positivity, gauge covariance, spatial-slice carriers, one-slab kernels, normalized physical transfer operators, and positive ground-state structure.

Completion criterion: satisfied for the finite root used by the downstream theorem chain.

---

# Phase 2 — Same-root scalar continuum OS construction

**Status: Integrated as a scalar observable lane.**

Canonical route:

```text
finite Wilson scalar readout
  -> rational/continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert completion
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint Hamiltonian
  -> normalized vacuum and vacuum-orthogonal sector.
```

Boundary: this is not yet the complete four-dimensional Yang--Mills gauge field/state.

---

# Phase 3 — Finite physical transfer and twelve-spatial routing

**Status: Integrated routing.**

The fixed-volume theorem tree contains the top/non-top decomposition, contraction, power decay, fixed-space characterization, coercivity, spectral confinement, resolvent and Green machinery, plus the actual six-right / six-left ground-state spatial conditional expectations.

The global implication route is already formalized:

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> physical transfer gap >= 3 kappa / 4.
```

Open input: a model-derived, scale-uniform positive `kappa`.

---

# Phase 4 — Sharp direct one-link control

**Status: Integrated through #3894, #3898, #3907.**

For the complete continuous-vacuum one-link law the repository proves a pairwise Harnack estimate, sharp normalized Haar comparison, and the variance lower bound with coefficient

```text
exp(-16 * beta).
```

No artificial second Harnack loss is introduced.

---

# Phase 5 — Transport into the actual ground-state joint law

**Status: Integrated through #3909 and #3921--#3952.**

The direct continuous-vacuum one-link law is transported almost everywhere to the actual ground-state split fiber. The resulting one-link variance/residual information is then integrated into the genuine joint `condExpL2` API on an explicit dense bounded concrete core.

Key boundary: no arbitrary `L²` quotient representative is evaluated pointwise.

---

# Phase 6 — Diagnose remote same-color aggregation

**Status: Obstruction integrated through #3969.**

The normalized same-color remote Doob laws admit a uniform single-source comparison and bounded-test influence estimate, but the naive same constant summed over all remote links grows with the number of remote sources.

Completion criterion: satisfied as a negative theorem. The constant-row-majorant route is closed.

---

# Phase 7 — Localize the true remote dependence

**Status: Integrated through #3978--#4016.**

The raw same-color Wilson target factor cancels exactly under a remote same-color source change. After continuous-vacuum integration, the remaining defect is localized to covariance between target-local and source-local observables.

The reference weight is replaced by a canonical pointwise positive continuous-vacuum representative and normalized to a genuine probability law, yielding the exact form

```text
remote physical defect
  = source scalar * Z^2 * Cov_nu_ref(target-local, source-local).
```

Completion criterion: exact localization achieved. Quantitative decay remains open.

---

# Phase 8 — Build the exact reference one-link conditional law

**Status: Integrated through #4019--#4077.**

This phase is now complete.

## 8.1 Fiber normalization

```text
#4019  positive/integrable literal fiber and normalized fiber law
#4024  fiber partition = singleton marginal
#4027  exact normalized density and base-point invariance
#4030  exact local normalization identity
#4035  full normalized reference-law Fubini compatibility
```

## 8.2 Heat-bath kernel

```text
#4039  measurable full-space heat-bath Markov kernel + stationarity
#4042  exact kernel idempotence
#4045  factor heat-bath projection through off-fiber restriction
#4048  proper off-fiber Markov kernel
```

## 8.3 Conditional law and RCD

```text
#4054  setwise conditional identity
#4057  nonnegative conditional integral identity
#4060  integrable real conditional integral identity
#4066  conditional-expectation representative
#4070  a.e. equality with Mathlib condExpKernel / RCD
#4077  transport doobBestConstantSquaredResidual and evariance
```

Completion criterion: satisfied. Do not reopen measurability/RCD existence unless a later theorem exposes a genuinely missing assumption or carrier bridge.

---

# Phase 9 — Expose the C5 conditional fiber as a raw-Doob composition

**Status: Integrated by #4080.**

Define the raw one-link weight

```text
q_A(g) = local(A[fiber <- g]) * oneSlabKernel(A[fiber <- g], B[source <- k]).
```

Normalize it against compact Haar:

```text
nu_A = Normalize_Haar(q_A).
```

The literal C5 reference weight factors pointwise as

```text
Omega_cont(A[fiber <- g]) * q_A(g).
```

PR #4080 proves the nonzero/finite first normalization mass and the exact composition theorem for successive normalized Doob tilts. Therefore

```text
C5 reference fiber = Doob_{Omega_cont along fiber}(nu_A).
```

Permanent boundary:

```text
nu_A is the normalized one-slab raw C5 law.
It is not the full-4D Wilson singleLinkConditionalMeasure by definition or naming.
```

Completion criterion: satisfied.

---

# Phase 10 — Quantitative summable remote mixing

**Status: Open now.**

This is the present theorem frontier.

The required next chain is:

```text
actual reference RCD
+ exact C5 raw-Doob factorization
+ raw Wilson same-color locality
+ continuous-vacuum structure
  -> quantitative remote RCD comparison
  -> distance-sensitive or otherwise summable influence/covariance coefficient
  -> same-color row sum bounded independently of volume.
```

A valid theorem must improve on the constant remote coefficient already ruled insufficient by #3969. Merely repackaging the existing `exp(16 * beta)` pairwise bound cannot close this phase.

Preferred proof shape:

1. keep target-local and source-local factors explicit;
2. use the exact RCD rather than a heuristic conditional density;
3. exploit the raw-Doob split from #4080 before estimating the continuous-vacuum contribution;
4. derive a coefficient with geometric separation, finite interaction range, cancellation, or another summable structure;
5. prove the resulting same-color row bound without a factor proportional to volume.

Completion criterion:

```text
sup_target sum_source c(target,source) < 1
```

or another formally sufficient volume-independent block-coercivity criterion derived from the actual model.

---

# Phase 11 — Same-color and twelve-spatial coercivity

**Status: Open next.**

Once Phase 10 supplies a summable remote estimate:

```text
one-link conditional variance / influence
  -> one same-color block coercivity
  -> six right color blocks
  -> six left color blocks
  -> quantitative 12-spatial Poincare inequality.
```

The target output is a model-derived coefficient `kappa(H,N,beta) > 0` with a proof of the required scale behavior.

---

# Phase 12 — Uniform finite-volume physical gap

**Status: Open downstream; routing already integrated.**

Required target:

```text
exists kappa_* > 0,
  kappa_* <= kappa(H,N,beta)
```

uniformly over the relevant sequence of finite volumes/scales. The already-formalized routing then gives

```text
physical transfer gap >= 3 * kappa_* / 4.
```

A positive coefficient separately at each finite volume is not enough.

---

# Phase 13 — Thermodynamic / scaling-limit propagation

**Status: Open downstream.**

A uniform finite-volume gap must be transported through the relevant limiting physical carrier with stable Poincare/resolvent/Green control and a justified connection to the OS/Wightman spectral generator.

No claim of completion is made at this stage.

---

# Phase 14 — Clay-level completion

**Status: Open.**

The final target still requires, in a sufficiently rich same-root four-dimensional continuum Yang--Mills construction:

```text
existence of the required continuum field/state
Osterwalder--Schrader / Wightman structure
correct vacuum sector and nontriviality
physical Hamiltonian / energy-momentum interpretation
strict positive spectral lower bound above the vacuum
```

The repository must continue to distinguish these goals from the already-integrated scalar continuum observable lane.

---

# Immediate next action

Before starting the next theorem unit, re-observe the exact HEAD of

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

because this documentation merge may advance the branch pointer. The latest mathematical theorem baseline represented here is

```text
1696ba98d930c5f59293319fc562d057d4b7586e
```

The next unit should use the #4070/#4077 actual reference RCD together with #4080's exact raw-Doob factorization to derive the first genuinely summable remote conditional-law estimate.

Do **not** spend the next unit reproving Fubini, measurability, properness, conditional expectation, or RCD existence: those interfaces are now canonical.
