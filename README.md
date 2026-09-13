# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, block dynamics, and the mass-gap problem.

The repository is intentionally strict about provenance. It distinguishes:

- statements proved on the actual finite Wilson / ground-state model;
- almost-everywhere bridges between concrete representatives;
- abstract implication machinery that is already integrated;
- diagnostic obstructions that rule out tempting but insufficient routes;
- quantitative mixing / coercivity inputs that are still open;
- the substantially larger thermodynamic and continuum problem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The finite-volume program has progressed well beyond the former split-fiber frontier. The sharp `exp(-16 * beta)` one-link variance information has been integrated into the genuine ground-state joint `condExpL2` residual on a dense bounded concrete core, and that one-link residual is related to the genuine spatial-color residual.
>
> A naive same-color summation, however, was proved to carry an explicit remote-source cardinality loss. The active route therefore shifted to the actual remote-dependence mechanism: raw same-color Wilson locality, continuous-vacuum covariance localization, normalization to a genuine reference probability law, and exact one-link marginal / fiber normalization identities.
>
> The immediate open problem is now to prove **full-law one-link heat-bath / Fubini compatibility for the normalized continuous-vacuum reference law**, then obtain the measurable conditional-specification machinery needed to prove a summable or distance-sensitive covariance / influence bound. That is the missing input for volume-independent spatial-color coercivity.

---

## Repository status — 2026-09-13 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest mathematical baseline before this documentation refresh:
  697591e7984f96f07ed0acfbd709b0df301affbe

This is the normal merge of:
  PR #4030
  Bridge reference one-link normalization to singleton marginals

Exact theorem head merged by PR #4030:
  cf3ae6954150824c804959089f2a096aa5495ea9

Exact-head validation:
  PR Lean Fast Check #13744
  workflow run 34753572564
  completed / success

Public landing branch:
  main

Detailed proof order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as canonical theorem status. A documentation-only merge may advance that branch pointer without changing the mathematical baseline named above.

---

# Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> boundary and spatial-slice L2 carriers
  -> normalized physical one-slab transfer
  -> positive / strictly-positive ground-state structure
                                                               [INTEGRATED]

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson gauge-invariant scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Omega and complete Omega-perp
                                                               [INTEGRATED]

C. FINITE PHYSICAL / GROUND-STATE JOINT-LAW LANE

physical top/non-top decomposition
  -> finite-volume contraction / coercivity / resolvent / Green machinery
  -> ground-state one-slab joint probability law Pi
  -> 6 genuine right spatial conditional expectations
  -> 6 genuine left spatial conditional expectations
  -> genuine two-sided 12-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing
                                                               [INTEGRATED ROUTING]

D. SHARP ONE-LINK GROUND-STATE CONTROL

continuous-vacuum one-link weight Wc
  -> pairwise Harnack exp(16 beta)                         [#3894]
  -> sharp normalized Haar comparison                     [#3898]
  -> exp(-16 beta) one-link variance lower bound          [#3907]
  -> a.e. compatibility with actual joint split fiber     [#3909]
  -> actual split-fiber variance / residual transfer      [#3921, #3926]
                                                               [INTEGRATED]

E. GENUINE ONE-LINK condExpL2 BRIDGE

integrated split-fiber variance
  -> outer-context weighted integration                   [#3934]
  -> arbitrary outer-center residual bound                [#3936]
  -> Doob--Dynkin outer representative of condExpL2       [#3937]
  -> bounded concrete one-link sections                   [#3938]
  -> genuine joint L2 residual norm                       [#3942]
  -> dense bounded concrete core                          [#3949]
  -> all spatial links / color residual domination        [#3952]
                                                               [INTEGRATED ON BOUNDED CORE]

F. SAME-COLOR REMOTE-INFLUENCE DIAGNOSTICS

remote continuous-vacuum weight comparison                [#3954]
  -> normalized Doob comparison exp(16 beta)              [#3959]
  -> bounded-test influence coefficient                   [#3964]
  -> naive row majorant grows with number of remote links [#3969]
                                                               [OBSTRUCTION INTEGRATED]

G. LOCALITY -> COVARIANCE ROUTE

raw same-color Wilson local-factor cancellation            [#3978]
  -> raw kernel four-point cross-ratio K = 1
  -> continuous-vacuum integral normal form               [#3983]
  -> source-conditioned ratio is one-link local           [#3991, #3994]
  -> four-integral cross-ratio = weighted covariance      [#3997, #4000]
  -> target-local x source-local covariance form          [#4004]
                                                               [INTEGRATED]

H. NORMALIZED CONTINUOUS-VACUUM REFERENCE LAW

canonical positive reference weight                       [#4011]
  -> genuine normalized reference probability law         [#4016]
  -> physical remote defect = scalar * Z^2 * Cov_nu       [#4016]
  -> literal one-link normalized fibers                   [#4019]
  -> fiber partition = singleton marginal                 [#4024]
  -> exact normalized one-link density                    [#4027]
  -> marginal * fiber expectation = weighted marginal     [#4030]
                                                               [INTEGRATED]

I. PRESENT OPEN FRONTIER

#4030 local normalization identity
  -> full normalized reference-law heat-bath / Fubini invariance [OPEN NOW]
  -> measurable one-link conditional specification / RCD bridge  [OPEN NEXT]
  -> summable or distance-sensitive covariance / influence       [OPEN]
  -> volume-independent same-color block control                  [OPEN]
  -> six-right + six-left block coercivity                        [OPEN]
  -> quantitative E12 Poincare coefficient                        [OPEN]
  -> scale-independent kappa_*                                    [OPEN]
  -> physical transfer gap >= 3 kappa_*/4                         [ROUTING INTEGRATED]

J. THERMODYNAMIC / CONTINUUM BOUNDARY

uniform finite-volume physical gap
  -> thermodynamic / scaling-limit physical carrier               [OPEN]
  -> physical OS/Wightman spectral lower bound                    [OPEN]
  -> sufficiently rich same-root 4D continuum Yang--Mills state  [OPEN]
  -> correct vacuum structure / nontriviality                     [OPEN]
  -> Clay-level existence + mass gap                              [OPEN]
```

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite root is the interacting periodic-even compact special-unitary Wilson Gibbs model built from

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar probability as reference measure.

Canonical infrastructure includes lattice and plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge covariance and gauge-invariant observables, spatial-slice and boundary `L²` carriers, one-slab Wilson kernels, normalized physical transfer operators, and positive ground-state structure.

The interacting Wilson law is not silently replaced by product Haar measure at nonzero coupling. Haar enters through explicit comparison, coordinate-splitting, marginal, and pushforward theorems.

---

# 2. Same-root continuum OS lane

The repository contains a constructive scalar continuum OS route obtained from finite Wilson pushforwards:

```text
finite Wilson scalar readout
  -> reflection-completed rational-time paths
  -> tightness / subsequential continuum law
  -> continuum reflection positivity
  -> OS quotient / Hilbert completion
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint Hamiltonian
  -> normalized vacuum Omega / complete Omega-perp
```

This is a genuine same-root continuum observable process. It is **not** yet the complete four-dimensional continuum gauge field/state required for the Clay problem.

---

# 3. Finite physical transfer and twelve-spatial routing

At fixed finite volume the authoritative branch contains physical top/non-top decomposition, contraction and power decay, fixed-space characterization, coercivity, real spectral confinement, resolvent estimates, Green machinery, exact reduced-range statements, and relative Poincare control.

On the actual ground-state one-slab joint probability law it also contains the genuine conditional expectations

```text
P_0,...,P_5 = six right spatial conditional expectations
L_0,...,L_5 = six left spatial conditional expectations.
```

The integrated implication route is

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> raw physical one-slab squared-defect coercivity
  -> physical transfer gap >= 3 kappa / 4.
```

This route is already formalized. It does **not** generate the required model-derived positive `kappa` by itself.

---

# 4. Sharp local one-link control — PRs #3894 through #3926

The continuous physical-vacuum route gives a pointwise-positive complete one-link weight with the pairwise Harnack estimate

```text
Wc(g) <= exp(16 * beta) * Wc(h).
```

Direct normalization gives

```text
exp(-16 * beta) <= rho(g) <= exp(16 * beta)
exp(-16 * beta) * Haar <= nu <= exp(16 * beta) * Haar,
```

and therefore the sharp local variance estimate

```text
exp(-16 * beta) * evariance_Haar(X)
  <= evariance_nu(X).
```

The a.e. bridge of #3909 transports the normalized direct one-link law to the actual ground-state split target fiber without pointwise evaluation of an arbitrary quotient representative. PRs #3921 and #3926 then transfer the residual / extended-variance estimate to that actual split fiber for a.e. outer context, preserving the single `exp(-16 * beta)` factor.

These are finite-volume local statements. They do not by themselves imply color-block or global Poincare coercivity.

---

# 5. The genuine `condExpL2` bridge is no longer the frontier — PRs #3934 through #3952

The previous README stopped before the split-fiber information reached the actual joint conditional-expectation API. That bridge is now substantially integrated.

The canonical sequence is:

```text
#3934  integrate the sharp actual-fiber variance with the exact fiber mass
#3936  compare it with a context-dependent centered residual
#3937  factor genuine one-link condExpL2 through the retained outer context
#3938  insert that center for bounded concrete one-link sections
#3942  identify the centered integral with the genuine joint L2 residual norm
#3949  prove the bounded strongly measurable concrete core is dense
#3952  package the bounded-core theorem simultaneously across all spatial links
       and dominate each one-link residual by its genuine spatial-color residual.
```

The resulting local coercivity statement is therefore attached to the **actual ground-state joint law and genuine `condExpL2`**, not merely to a formal split-fiber law.

The current documentation does not claim an arbitrary-`L²` pointwise fiber theorem. The bounded concrete core and its density are explicit, and closure must be used at the Hilbert-space level rather than by evaluating arbitrary `L²` representatives pointwise.

---

# 6. Why naive color aggregation is insufficient — PRs #3954 through #3969

The next natural attempt was to compare normalized same-color one-link Doob laws under a remote source change.

The repository now proves:

```text
pointwise remote-weight comparison with factor exp(8 * beta)   [#3954]
normalized Doob-law mutual domination with exp(16 * beta)      [#3959]
bounded-test influence <= 2 * (K - 1) / (K + 1)               [#3964]
```

with `K = exp(16 * beta)` in the physical specialization.

PR #3969 then formalizes the decisive obstruction: if that same constant is simply assigned to every distinct same-color remote source, the row majorant is multiplied by the cardinality of the remote-source set. It is therefore not a volume-independent color contraction.

This changed the active strategy. The proof must extract **actual locality / decay / cancellation**, not merely repeat a uniform pairwise Harnack bound over all remote links.

---

# 7. The remote dependence is localized to covariance — PRs #3974 through #4004

The raw Wilson kernel has much stronger same-color locality than the continuous-vacuum law.

PR #3978 proves that changing a distinct same-color remote source leaves the target-local raw Boltzmann factor unchanged and gives a raw four-point cross-ratio equality `K = 1`. This is an exact raw-kernel statement only; integration against the physical vacuum can reintroduce dependence.

The subsequent chain identifies precisely where that dependence lives:

```text
#3983  expose the continuous-vacuum left-boundary integral normal form
#3991  localize the source-conditioned kernel cross-ratio
#3994  factor the source likelihood ratio into a source-local Wilson crossing ratio
#3997  rewrite a four-integral cross-ratio defect as an unnormalized covariance numerator
#4000  instantiate that covariance identity on the physical continuous-vacuum defect
#4004  extract the A-independent source scalar and leave
       target-local ratio x source-local ratio under one reference weight.
```

Schematically, the nontrivial remote defect is no longer an opaque global ratio. It is a covariance between a target-local observable and a source-local observable under a common left-boundary reference weight.

This is the correct location for any future target-source distance decay.

---

# 8. Genuine normalized reference probability law — PRs #4011 and #4016

PR #4011 replaces the arbitrary `L²` vacuum representative in that covariance weight by the canonical pointwise continuous vacuum representative using an a.e. weighted-covariance transport theorem.

The resulting positive reference weight has the form

```text
w_ref(A) = Omega_cont(A) * L_g2(A) * Q_k(A).
```

PR #4016 proves only the regularity needed for normalization. Instead of forcing an expensive full-product continuity theorem, it uses

```text
0 < L_g2 <= exp(8 * beta)
0 < Q_k <= 1
Omega_cont integrable
```

to dominate `w_ref` by `exp(8 * beta) * Omega_cont`.

It then constructs a genuine normalized probability law `nu_ref` and proves the exact normalization formula

```text
weighted covariance numerator = Z^2 * covariance under nu_ref.
```

Hence the physical same-color remote four-point defect is represented exactly as

```text
A-independent source scalar
  * Z^2
  * Cov_nu_ref(target-local ratio, source-local ratio).
```

No identification of `nu_ref` with the Wilson Gibbs law is made.

---

# 9. One-link conditional-specification algebra for the reference law — PRs #4019 through #4030

The newest canonical sequence builds the law-side one-link fiber carefully without prematurely calling it a regular conditional distribution.

For a selected spatial link `fiber` and background configuration `A`:

```text
#4019
  define the literal fiber weight
    g |-> w_ref(A[fiber <- g]);
  prove positivity, Haar integrability, positive partition function;
  define the normalized literal fiber probability law.

#4024
  prove
    ENNReal.ofReal Z_fiber(A)
      = lmarginal_{ {fiber} } rho_ref(A),
  where rho_ref = ENNReal.ofReal o w_ref.

#4027
  prove the exact normalized density representation
    nu_fiber(A)
      = Haar.withDensity
          (g |-> rho_ref(A[fiber <- g]) /
            lmarginal_{ {fiber} } rho_ref(A));
  prove invariance under changing the stored background value at `fiber`.

#4030
  for every nonnegative measurable F, prove
    lmarginal rho_ref(A)
      * integral F(A[fiber <- g]) d nu_fiber(A)
    = lmarginal (rho_ref * F)(A).
```

This is the exact local normalization / disintegration algebra needed for outer Fubini arguments.

It still does **not** assert that `A |-> nu_fiber(A)` is already a regular conditional distribution of the normalized full reference law.

---

# 10. Present mathematical frontier: full-law heat-bath / Fubini compatibility

The next coherent theorem unit should consume #4030 at the full product-measure level.

The target is an exact invariance identity of the form

```text
integral_A [ integral_g F(A[fiber <- g]) d nu_fiber(A) ] d nu_ref(A)
  = integral_A F(A) d nu_ref(A)
```

for nonnegative measurable `F`, or an equivalent unnormalized Fubini identity from which this normalized statement follows.

This theorem should be proved from:

```text
#4030 fiber normalization identity
+ singleton-marginal / product-Haar Fubini machinery
+ the exact full reference density
+ the already-proved base-point invariance of the fiber law.
```

Only after this compatibility is established should the code specialize a measurable Markov-kernel / conditional-expectation or RCD statement. The measurable-kernel claim and the RCD claim are separate obligations; neither should be inferred from a pointwise normalized density formula alone.

---

# 11. What must come after full-law compatibility

The global finite-volume gap route now depends on obtaining a **summable same-color remote-dependence estimate** from the normalized reference law.

A successful next layer may take the form of one of the following equivalent-strength mechanisms:

```text
distance-sensitive covariance decay
summable Dobrushin / influence coefficients
block-level contraction using same-color geometry
another model-derived estimate that avoids link-count growth.
```

What is not enough is already formalized:

```text
one uniform nonzero influence constant per remote source
  -> row sum proportional to the number of remote sources
  -> no volume-independent color contraction.
```

The intended global order is therefore

```text
full reference-law one-link compatibility
  -> measurable conditional specification
  -> quantitative covariance / influence decay
  -> volume-independent same-color block residual control
  -> six right + six left blocks
  -> quantitative E12 coercivity
  -> identify the relevant common-fixed sector
  -> finite-volume model-derived kappa(H,N,beta) > 0
  -> scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4.
```

---

# 12. What is still not proved

The following distinctions remain mandatory:

```text
bounded-core one-link condExpL2 coercivity
  != arbitrary-L2 pointwise fiber theorem

literal normalized one-link fiber
  != regular conditional distribution of the full reference law

full-law heat-bath invariance
  != quantitative remote mixing or decay

uniform pairwise remote comparison
  != summable Dobrushin row bound

raw Wilson same-color K = 1
  != continuous-vacuum or physical Doob K = 1

covariance localization
  != covariance decay

one-link coercivity
  != volume-independent color-block coercivity

positive finite-volume coefficient
  != scale-independent coefficient

qualitative common-fixed characterization
  != final vacuum-sector identification

uniform finite-volume transfer gap
  != continuum mass gap

same-root scalar continuum process
  != full 4D continuum Yang--Mills field/state

one selected positive exact mode
  != lower spectral bound on the whole physical orthogonal sector.
```

---

# 13. Current execution order

```text
1. prove full normalized-reference one-link heat-bath / Fubini compatibility
   from #4030 and singleton-marginal product-Haar integration;
2. construct or specialize the measurable one-link heat-bath Markov kernel and,
   only with the required measurability/disintegration receipts, state the
   corresponding conditional-law / RCD theorem;
3. use that specification to prove a target-source covariance or influence
   estimate that is summable over a same-color remote set;
4. explicitly test the bound for volume dependence; reject any coefficient
   whose row sum grows like the number of links;
5. convert the summable remote control into one spatial color-block residual
   coercivity on the actual ground-state joint carrier;
6. prove the six-right and six-left block estimates;
7. assemble quantitative twelve-block Dirichlet control;
8. identify the exact twelve-block common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;
9. prove a positive finite-volume twelve-block Poincare coefficient and then
   a scale-independent kappa_*;
10. invoke the integrated E12 -> E6 -> raw physical defect -> transfer-gap route;
11. propagate a uniform physical gap through a same-root thermodynamic /
    continuum construction and only then address the physical OS/Wightman gap.
```

---

## Repository discipline

For theorem development the intended workflow is:

```text
exact canonical SHA
  -> branch from that SHA
  -> Draft PR
  -> intentional RED when introducing a new proof obligation
  -> exact-head CI
  -> write-freeze while CI is in progress
  -> distinguish cache / missing-.olean diagnostics from the first genuine Lean error
  -> repair the mathematical / elaboration root cause without strengthening assumptions
  -> exact-head GREEN
  -> merge with expected head SHA fixed
  -> verify merge commit and canonical branch pointer.
```

No open PR, memory summary, README statement, synthetic merge SHA, or nonterminal CI result outranks the exact canonical theorem tree.

---

## Navigation

- `ROADMAP.md` — ordered proof program and completion criteria.
- `MGAP4D/MathlibAnalytic/` — Lean/mathlib theorem development.
- `docs/` — supporting bridge and review documentation.
- `EXTERNAL_REVIEW_CHECKLIST.md` — carrier / claim-boundary review checklist.

The repository treats exact theorem provenance, negative/obstruction results, and explicit claim boundaries as part of the proof artifact itself.