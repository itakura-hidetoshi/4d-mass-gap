# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills existence and the mass-gap problem.

The repository is deliberately strict about theorem provenance and claim boundaries. Its purpose is not to turn an abstract spectral implication into a physical claim, but to keep every physical conclusion connected to the actual finite Wilson root through explicit theorem-level bridges.

> **Current claim boundary.** This repository does **not** yet constitute a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem. It contains a large formal same-root construction, including finite Wilson reflection-positive data, continuum OS/Hamiltonian infrastructure, physical transfer-mode machinery, and increasingly concrete SU(2) finite-to-continuum mode transport. Remaining model-facing seams are kept explicit rather than hidden in certificate fields.

## Authoritative status — 2026-09-02 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Current canonical exact SHA:
  ed83a9510cc20aee178d7070acb629b44866f2d7

Latest canonical theorem unit:
  PR #3127
  Identify SU2 boundary-pair closure with completed transfer graph
```

Only theorem results merged into the authoritative theorem carrier count as current proof status.

---

## Proof picture in one view

```text
ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection positivity / finite OS geometry
  -> gauge-invariant Wilson observables
  -> same-root scalar continuum process
  -> continuum OS positivity
  -> OS Hilbert carrier
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ excitation sector

PHYSICAL TRANSFER / MODE LANE

actual finite Wilson boundary transfer
  -> completed boundary realization
  -> positive-time represented OS carrier
  -> direct boundary-pair map
  -> closure of its range
  -> completed finite Wilson transfer graph
  -> genuine finite OS transfer eigenmodes
  -> common-carrier finite-to-continuum transfer
  -> continuum time-one eigenmodes
  -> graph-closed continuum Hamiltonian modes

EXACT-GAP SPECIALIZATION

cutoff physical one-slice eigenvalues μ_n
  -> μ_n -> exactGapClusterContractionRatio
  -> exactGapClusterContractionRatio = exp(-exactGapValueReal)
  -> continuum time-one eigenvalue
  -> Hamiltonian mode with energy exactGapValueReal

CURRENT STRUCTURAL FRONTIER

replace remaining model-facing realization / closure / convergence seams
by theorems derived from the actual finite Wilson construction;
then close the full same-root physical carrier and establish the
positive spectral lower-bound / existence statements required for a
Clay-level conclusion.
```

---

## What has changed since the earlier roadmap

The August 2026 roadmap correctly identified the finite Wilson shared-boundary transfer as the decisive physical lane. Since then the formal development has moved substantially beyond a purely abstract Poincare-gap interface.

The current canonical SU(2) spine now contains theorem-level machinery that:

- realizes physical one-slice transfer information on the finite Wilson OS Hilbert carrier;
- packages the time-zero/time-one realization as one positive-time boundary-pair closure problem rather than unrelated endpoint approximations;
- identifies the closure of the direct positive-time boundary-pair range with the **completed finite Wilson transfer graph**;
- connects the resulting finite OS eigenvector to the canonical common-carrier approximant;
- passes convergent cutoff-dependent transfer eigenvalues to a continuum OS time-one eigen-equation;
- converts a continuum time-one eigenvalue `mu` into a graph-closed Hamiltonian mode of energy `-log mu`;
- specializes this route to `exactGapClusterContractionRatio = exp(-exactGapValueReal)` without silently introducing a new numerical literal.

PR #3127 is particularly important structurally: the positive-time boundary-pair closure is no longer merely included in the completed transfer graph; it is identified with that graph exactly.

This does **not** by itself prove ambient boundary surjectivity, a full four-dimensional continuum gauge field, vacuum uniqueness, a universal positive spectral lower bound, or the Clay theorem. Those remain separate obligations.

---

## Same-root OS/Hamiltonian construction

The canonical construction includes a genuine same-root scalar continuum law obtained from finite Wilson observables and a real OS reconstruction with

```text
rational and real contraction semigroups
dense generator domain
graph-closed self-adjoint Hamiltonian
normalized vacuum Ω
vacuum-orthogonal excitation carrier Ω⊥
resolvent / Yosida / spectral infrastructure
```

The scalar continuum process is an actual same-root continuum observable law, but it is not yet the complete four-dimensional continuum gauge connection.

---

## Finite covariance lane: useful theorem, not the final mechanism

The repository also contains a genuine finite-volume separated-support covariance theory based on the actual Wilson measure. The active-TV/Dobrushin majorant is formally diagnosed as a high-temperature mechanism: its contraction ratio cannot remain below one along a scaling with `beta_n -> +∞`.

Accordingly, the current physical mass-gap program does **not** treat that Dobrushin estimate as the intended continuum mass-gap mechanism. It remains useful as a finite theorem, a localization tool, and a diagnostic control lane.

---

## Current mathematical frontier

The next work should be judged by whether it removes a genuine model-facing seam on the same physical carrier. In particular:

1. derive the remaining positive-time/boundary realization hypotheses directly from the finite Wilson construction wherever they are still assumptions;
2. tighten the common-carrier approximation and convergence data until the continuum eigenmode is generated entirely from same-root finite data;
3. prove the positive lower-bound statement for the full vacuum-orthogonal physical spectrum, not merely existence of selected modes;
4. complete a sufficiently rich four-dimensional continuum Yang--Mills carrier with Euclidean covariance, gauge-invariant local content, regularity, reflection positivity, vacuum structure, and nontriviality;
5. only then state a Clay-level existence-and-mass-gap theorem.

The governing rule is:

```text
physical conclusion
  <= theoremically derived same-root data
  <= actual finite Wilson model
```

not

```text
physical conclusion
  <= opaque certificate containing the desired estimate.
```

---

## Exact-value claims

The repository contains an exact-gap spectral route. Its current public specialization produces a continuum Hamiltonian mode with energy `exactGapValueReal` through the transfer ratio

```text
exactGapClusterContractionRatio = exp(-exactGapValueReal).
```

This should not be confused with a theorem that the **entire** non-vacuum spectrum is bounded below by that value, nor with a completed Clay theorem. Numerical identifications must remain attached to explicit theorem-level provenance.

---

## Broader research horizon: universal relational structure

MGAP4D is a mathematical-physics repository, so its authoritative claims remain Yang--Mills claims. A broader research program developed in the companion **KuuOS** work asks whether contextual transport, equivalence, higher coherence, descent, and presentation invariance admit a universal characterization.

The long-term target is a representation/universality principle of the schematic form

```text
contextual system
  + admissible equivalences
  + higher coherence
  + descent
  + presentation invariance
    -> essentially unique factorization through a universal relational object.
```

MGAP4D provides a demanding realization domain for that philosophy: gauge equivalence, OS reconstruction, finite-to-continuum transport, quotient/completion, and spectral information all force careful separation between presentation-dependent data and invariant physical content.

This broader universality program is a **research horizon**, not an additional theorem claim of this repository. Its relevance to future AI is likewise conceptual at present: a sufficiently general theory of coherent contextual transport could provide mathematical language for representation-independent state, memory, world-model transport, and multi-agent consistency.

---

## Validation and repository discipline

```text
ordinary proof PRs start from the exact canonical SHA
validation and replacement heads are kept distinct when required
CI is accepted only when workflow / job / exact Lean step are completed/success
queued or in-progress heads are not modified
changes are additive / tighten-only
sorry / admit / axiom / placeholder constants are forbidden
physical assumptions are not weakened merely to close a proof
normal merges preserve proof-head provenance
post-merge canonical SHA is re-read from GitHub and becomes authoritative
```

The repository's strongest asset is not the number of formal files but the explicit provenance chain from physical model to theorem.

## What to read next

See [`ROADMAP.md`](ROADMAP.md) for the ordered development plan from the current canonical frontier.