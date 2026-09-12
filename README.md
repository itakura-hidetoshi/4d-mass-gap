# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, and the mass-gap problem.

The repository is intentionally strict about provenance. It distinguishes:

- results proved on the actual finite Wilson model;
- model-facing bridges proved only almost everywhere;
- abstract implication machinery already integrated;
- quantitative hypotheses that are still open;
- the substantially larger thermodynamic / continuum problem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The local finite-volume program has advanced beyond one-link Harnack and beyond the a.e. identification of the direct continuous-vacuum one-link law with the actual ground-state split fiber. The sharp `exp(-16 beta)` one-link variance / residual control is now transferred to the **actual ground-state joint split one-link fiber for a.e. outer context**.
>
> The immediate open problem is to turn that fiberwise theorem into coercivity for the **genuine ground-state `condExpL2` residual**, integrate it over the actual joint carrier without losing the sharp constant unnecessarily, and then aggregate one-link residuals to spatial color blocks and the twelve-block Dirichlet form.

---

## Repository status — 2026-09-13 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest mathematical baseline before this documentation refresh:
  282913e02c660d0181ee69e552bf374549adc8d4

This is the normal merge of:
  PR #3926
  Transfer sharp one-link variance to ground-state joint split fibers

Its first parent is:
  4cce50198af53abd6449edafcd16f0fab4f4b2e3
  normal merge of PR #3921
  Transfer sharp one-link variance to actual ground-state split fiber

Exact proof heads:
  PR #3921: 1c755f07b1add1480ab1ae8287d847da8462d1bb
  PR #3926: db95f664ed50084cd68fc42621793d97189c0d81

Exact-head validation:
  PR #3921: PR Lean Fast Check #13632 = completed / success
             workflow run 34699024449
  PR #3926: PR Lean Fast Check #13637 = completed / success
             workflow run 34722528934

Public landing branch:
  main

Detailed proof order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as canonical theorem status. Documentation-only merges may advance that branch pointer without changing the mathematical baseline named above.

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
  -> left/right boundary L2 isometries
  -> 6 genuine right spatial conditional expectations
  -> 6 genuine left spatial conditional expectations
  -> genuine two-sided 12-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing
                                                               [INTEGRATED ROUTING]

D. SHARP CONTINUOUS-VACUUM ONE-LINK LANE

complete one-link weight Wc(g)
  -> strict positivity
  -> pairwise Harnack
       Wc(g) <= exp(16 beta) Wc(h)                         [#3894]
  -> normalize rho = Wc / integral Wc dHaar
  -> exp(-16 beta) <= rho(g) <= exp(16 beta)               [#3898]
  -> exp(-16 beta) Haar <= nu <= exp(16 beta) Haar         [#3898]
  -> sharp normalized one-link variance lower bound
       exp(-16 beta) Var_Haar <= Var_nu                    [#3907]
                                                               [INTEGRATED]

E. A.E. BRIDGE TO THE ACTUAL JOINT SPLIT FIBER

continuous-vacuum direct normalized one-link law
  -> target/off-target Haar coordinate split
  -> a.e. equality with legacy ground-state split target fiber
  -> exact target-evaluation Measure.map back to SU(N)
                                                               [#3909, INTEGRATED]

F. ACTUAL GROUND-STATE SPLIT-FIBER VARIANCE

sharp direct one-link residual / variance
  + #3909 a.e. fiber compatibility
  -> a.e. fixed-center squared-residual lower bound
  -> a.e. best-constant squared-residual lower bound
  -> a.e. evariance lower bound on the actual split fiber
                                                               [#3921, INTEGRATED]

actual normalized split target fiber
  -> exact target evaluation / direct fiber IdentDistrib
  -> exact transport of evariance
  -> sharp exp(-16 beta) lower bound on the actual joint split fiber
                                                               [#3926, INTEGRATED]

G. PRESENT OPEN FRONTIER

a.e. actual joint split-fiber variance
  -> genuine joint condExpL2 residual coercivity                  [OPEN NOW]
  -> integrate over outer contexts on the actual joint carrier   [OPEN NOW]
  -> one spatial color-block residual                            [OPEN NOW]
  -> six-right + six-left block control                          [OPEN NOW]
  -> quantitative E12 coercivity                                [OPEN NOW]
  -> identify relevant 12-block common-fixed sector              [OPEN NOW]
  -> positive scale-independent kappa_*                          [OPEN NOW]
  -> physical transfer gap >= 3 kappa_*/4                        [ROUTING INTEGRATED]

H. THERMODYNAMIC / CONTINUUM BOUNDARY

uniform finite-volume physical gap
  -> thermodynamic / scaling-limit physical carrier              [OPEN]
  -> physical OS/Wightman spectral lower bound                   [OPEN]
  -> sufficiently rich same-root 4D continuum Yang--Mills state [OPEN]
  -> correct vacuum structure / nontriviality                    [OPEN]
  -> Clay-level existence + mass gap                             [OPEN]
```

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite root is the interacting periodic-even compact special-unitary Wilson Gibbs model built from

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar probability as reference measure.

Canonical infrastructure includes lattice and plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge covariance and gauge-invariant observables, spatial-slice and boundary `L²` carriers, one-slab Wilson kernels, normalized physical transfer operators, and positive ground-state structure.

The interacting Wilson law is not silently replaced by product Haar measure at nonzero coupling. Haar enters through explicit comparison, coordinate-splitting, and pushforward theorems.

---

# 2. Same-root continuum OS lane

The repository already contains a constructive scalar continuum OS route obtained from finite Wilson pushforwards:

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

On the actual ground-state one-slab joint probability law the repository also contains genuine conditional expectations:

```text
P_0,...,P_5 = six right spatial conditional expectations
L_0,...,L_5 = six left spatial conditional expectations
```

These form the genuine two-sided twelve-spatial family used by the physical routing.

The integrated implication chain is

```text
12-block Poincare coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> raw physical one-slab squared-defect coercivity
  -> physical transfer gap >= 3 kappa / 4.
```

This route is already formalized. It does **not** generate the required model-derived positive `kappa` by itself.

---

# 4. Sharp continuous-vacuum one-link control — PRs #3894, #3898, #3907

The complete direct ground-state one-link weight uses the canonical continuous physical-vacuum representative. The canonical chain is

```text
Wc(g) > 0
Wc(g) <= exp(16 beta) Wc(h)
```

followed by direct normalization. If

```text
mu  = normalized compact Haar on SU(N)
Z   = integral Wc dmu
rho = Wc / Z
nu  = rho * mu
R   = exp(16 beta),
```

then

```text
0 < Z < infinity
R^{-1} <= rho(g) <= R
R^{-1} mu <= nu <= R mu.
```

The pairwise Harnack inequality is integrated directly, so the proof pays the Harnack factor once rather than introducing an artificial `exp(32 beta)` loss.

For Haar-`L²` observables, the normalized measure comparison yields the sharp local variance estimate

```text
R^{-1} * evariance_mu(X) <= evariance_nu(X),
R^{-1} = exp(-16 beta).
```

This remains the basic quantitative local constant for the current block-dynamics program.

---

# 5. A.e. compatibility with the actual ground-state split fiber — PR #3909

The continuous-vacuum direct law and the legacy ground-state joint density use vacuum representatives that agree only almost everywhere. The correct bridge is therefore a.e., not pointwise.

The integrated theorem:

```text
reconstructs the complete right boundary from retained off-target coordinates;
uses Omega_c = Omega almost everywhere under spatial-slice Haar;
transports that equality through the exact target/off-target Haar split;
identifies normalized split target fibers for a.e. outer context;
proves exact singleton-target Measure.map transport back to SU(N).
```

The exceptional contexts remain explicit. This theorem does not identify the fiber as a regular conditional distribution and does not justify pointwise evaluation of an arbitrary `L²` quotient representative.

---

# 6. Sharp variance on the actual ground-state split fiber — PRs #3921 and #3926

This is the major update since the previous README.

PR #3921 consumes the #3909 a.e. measure equality and transfers the direct sharp residual / variance estimates to the actual ground-state split carrier. The integrated files include:

```text
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkContextVarianceTransfer.lean
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkJointVarianceTransfer.lean
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointObservableOneLinkVariance.lean
```

The resulting theorem layer includes a.e. fixed-center residual control, a.e. best-constant residual control, and a.e. extended-variance control while preserving the single `exp(-16 beta)` factor.

PR #3926 adds the focused actual split-fiber transport theorem in

```text
PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkVarianceTransfer.lean
```

Its proof uses the #3909 a.e. pushforward identity together with `ProbabilityTheory.IdentDistrib` for target evaluation, transports `evariance` exactly, and applies the sharp #3907 direct theorem.

Schematically, for Haar-`L²` `X`, for a.e. outer context,

```text
exp(-16 beta) * evariance_Haar(X)
  <= evariance_actual_ground_state_split_fiber(X o targetEvaluation).
```

This is now canonical finite-volume local information on the **actual** ground-state split fiber.

---

# 7. Present mathematical frontier: from fibers to `condExpL2`

The immediate task is no longer to transfer the one-link variance estimate to the actual split fiber; that step is integrated.

The next theorem must connect the a.e. fiberwise statement to the genuine conditional-expectation residual on the actual ground-state joint `L²` carrier:

```text
a.e. split-fiber variance lower bound
  + actual joint disintegration / conditional-expectation API
  + measurable outer-context integration
  -> genuine one-link condExpL2 residual coercivity.
```

The proof must keep the distinction between these statements explicit:

```text
fiberwise a.e. measure equality
  != an RCD identification

fiberwise evariance lower bound
  != global condExpL2 residual coercivity

integrating an a.e. fiber theorem
  != permission to evaluate arbitrary L2 representatives pointwise.
```

The preferred route is to use existing measure/disintegration and `condExpL2` infrastructure, preserve measure-specific a.e. quantifiers, and avoid introducing an extra Harnack loss unless mathematically forced.

After that bridge the proof can aggregate one-link residuals across the actual spatial matching / color geometry.

---

# 8. From one-link residuals to the global finite-volume gap

The constructive target after the `condExpL2` bridge is

```text
genuine one-link residual coercivity
  -> one spatial color-block residual
  -> six right block estimates
  -> six left block estimates
  -> quantitative E12 Dirichlet control
  -> identify the exact common-fixed sector
  -> finite-volume Poincare coefficient kappa(H,N,beta) > 0
  -> scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4.
```

The decisive quantitative milestone is

```text
exists kappa_* > 0, for every relevant physical scale n,
  kappa_* * ||z||^2 <= E12_n(z)
```

on the correct common-fixed-space orthogonal complement, with `kappa_*` derived from the actual Wilson / ground-state model.

---

# 9. What is still not proved

The following distinctions remain mandatory:

```text
a.e. actual split-fiber variance
  != global conditional-expectation coercivity

one-link coercivity
  != color-block coercivity

positive finite-volume coefficient
  != scale-independent coefficient

local Harnack / Doeblin / variance control
  != global L2 Poincare theorem

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

# 10. Current execution order

```text
1. connect the canonical #3921/#3926 a.e. actual split-fiber variance
   theorem to the genuine ground-state joint condExpL2 residual;
2. integrate the one-link residual estimate over outer contexts without
   losing the sharp exp(-16 beta) coefficient unnecessarily;
3. aggregate genuine one-link residuals to one spatial color block using
   the actual matching / disjoint-update geometry;
4. prove the six-right and six-left block estimates on the same joint carrier;
5. assemble quantitative twelve-block Dirichlet control;
6. identify the exact twelve-block common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;
7. prove a positive finite-volume twelve-block Poincare coefficient;
8. make the coefficient scale-independent, or identify precisely where a
   proposed coefficient degenerates;
9. invoke the integrated E12 -> E6 -> raw defect -> transfer-gap route;
10. propagate a uniform physical gap through a same-root thermodynamic /
    continuum construction and only then address the physical OS/Wightman gap.
```

---

## Repository discipline

For theorem development the intended workflow is:

```text
exact canonical SHA
  -> branch from that SHA
  -> Draft PR
  -> exact-head CI
  -> write-freeze while CI is in progress
  -> inspect first genuine Lean failure on RED
  -> minimal mathematical fix
  -> exact-head GREEN
  -> merge with head SHA fixed
  -> verify merge commit / canonical pointer.
```

No open PR, memory summary, README statement, or CI result outranks the exact canonical theorem tree.

---

## Navigation

- `ROADMAP.md` — ordered proof program and completion criteria.
- `MGAP4D/MathlibAnalytic/` — Lean/mathlib theorem development.
- `docs/` — supporting bridge and review documentation.
- `EXTERNAL_REVIEW_CHECKLIST.md` — carrier / claim-boundary review checklist.

The repository treats exact theorem provenance and explicit claim boundaries as part of the proof artifact itself.