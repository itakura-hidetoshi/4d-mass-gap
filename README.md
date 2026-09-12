# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, ground-state conditional expectations, and the mass-gap problem.

The project is deliberately strict about theorem provenance. It separates what is already proved on the actual finite Wilson model from implication machinery, open quantitative hypotheses, and the much larger remaining continuum problem.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current model-facing proof has advanced to a sharp, volume-independent one-link analysis for the physical continuous vacuum, and that one-link law is now bridged almost everywhere back to the actual ground-state joint one-link fiber.
>
> The immediate open problem is no longer to obtain a local Harnack estimate. It is to convert the now-canonical sharp one-link variance control into coercivity for the **actual ground-state conditional-expectation dynamics**, aggregate it to spatial blocks / colors, identify the relevant common-fixed sector, and obtain a positive scale-independent twelve-block Poincaré coefficient.

---

## Repository status — 2026-09-12 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest mathematical checkpoint before this documentation-only refresh:
  f74b992b8548734af7225c64314ad8fa18e21c0f

This is the normal merge of:
  PR #3909
  Identify continuous-vacuum and joint one-link fibers a.e.

Exact proof head merged by PR #3909:
  12445afbe35e0ed9645234355a4074ffce440243

Exact-head validation:
  PR Lean Fast Check #13627 = completed / success
  Run changed Lean fast check = success

Public landing branch:
  main

Detailed proof order:
  ROADMAP.md
```

Only results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as canonical theorem status.

---

# Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L² carriers
  -> normalized physical one-slab transfer
  -> positive / strictly-positive ground-state transfer structure

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson gauge-invariant scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C₀ contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. FINITE PHYSICAL / JOINT-LAW LANE

physical top/non-top decomposition
  -> finite-volume contraction / coercivity / resolvent / Green machinery
  -> ground-state one-slab joint law Π
  -> left/right boundary L² isometries
  -> six genuine right spatial conditional expectations
  -> six genuine left spatial conditional expectations
  -> two-sided twelve-spatial conditional-expectation family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing

D. SHARP CONTINUOUS-VACUUM ONE-LINK LANE

complete physical one-link weight W_c(g)
  -> strict positivity
  -> pairwise Harnack
       W_c(g) <= exp(16 beta) W_c(h)                    [Integrated: #3894]
  -> normalization Z = integral W_c dHaar
  -> normalized density rho = W_c/Z
       exp(-16 beta) <= rho(g) <= exp(16 beta)          [Integrated: #3898]
  -> volume-independent measure comparison
       exp(-16 beta) Haar <= nu <= exp(16 beta) Haar    [Integrated: #3898]
  -> sharp normalized one-link variance lower bound
       exp(-16 beta) Var_Haar <= Var_nu                [Integrated: #3907]

E. ACTUAL JOINT-FIBER COMPATIBILITY

continuous-vacuum direct normalized one-link law
  -> target/off-target Haar coordinate split
  -> a.e. equality with the legacy ground-state split target fiber
  -> exact target-coordinate Measure.map back to SU(N)
  -> a.e. compatibility with the actual joint one-link fiber          [Integrated: #3909]

F. PRESENT OPEN FRONTIER

consume the a.e. compatibility theorem inside the actual joint
conditional-expectation/disintegration lane                           [OPEN NOW]
  -> transfer the sharp exp(-16 beta) one-link variance estimate       [OPEN NOW]
  -> aggregate one-link variances to spatial color blocks              [OPEN NOW]
  -> aggregate right-six + left-six to the 12-block Dirichlet form     [OPEN NOW]
  -> identify the relevant 12-block common-fixed sector                [OPEN NOW]
  -> prove positive scale-independent kappa                            [OPEN NOW]
  -> physical transfer gap >= 3 kappa / 4                              [ROUTING INTEGRATED]

G. CONTINUUM / CLAY BOUNDARY

uniform finite-volume physical gap
  -> stable thermodynamic / scaling-limit physical carrier             [OPEN]
  -> physical OS/Wightman spectral lower bound                         [OPEN]
  -> sufficiently rich same-root 4D continuum Yang--Mills field/state [OPEN]
  -> correct vacuum structure / nontriviality                          [OPEN]
  -> Clay-level existence + mass gap                                   [OPEN]
```

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite model is built from

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized compact Haar probability and the interacting periodic-even Wilson Gibbs law.

Canonical infrastructure includes lattice / plaquette geometry, Wilson action and Gibbs measure, reflection positivity, gauge covariance and gauge-invariant observables, spatial-slice and boundary `L²` carriers, one-slab Wilson kernels, and normalized physical transfer operators.

The interacting Wilson law is never silently replaced by product Haar measure at nonzero coupling.

---

# 2. Same-root continuum OS lane

The repository already contains a constructive scalar continuum OS route obtained from finite Wilson pushforwards:

```text
finite Wilson scalar readout
  -> reflection-completed rational-time paths
  -> tightness / Prokhorov subsequential continuum law
  -> continuum reflection positivity
  -> OS quotient / Hilbert completion
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint Hamiltonian
  -> normalized vacuum Ω / complete Ω⊥
```

This is a genuine same-root continuum observable process. It is **not** yet the complete four-dimensional continuum gauge field on `ℝ⁴`.

---

# 3. Finite physical transfer and ground-state joint-law machinery

At fixed finite-volume data the canonical branch contains substantial transfer and spectral machinery, including strict non-top contraction, power decay, strong convergence, fixed-space characterization, coercivity, real spectral confinement, resolvent estimates, a Green operator, exact reduced-range statements, and relative Poincaré control.

The newer model-facing route works on the actual physical ground-state one-slab joint probability law. On that carrier the repository has genuine conditional expectations rather than an abstract replacement projection family:

```text
P_0,...,P_5 = six right spatial conditional expectations
L_0,...,L_5 = six left spatial conditional expectations
```

They form a genuine two-sided twelve-spatial family. The repository also contains the concrete routing

```text
12-block Poincaré coefficient kappa
  -> six-spatial frame coefficient 2 kappa
  -> raw physical one-slab squared-defect coercivity
  -> physical transfer-gap lower bound >= 3 kappa / 4.
```

That routing is integrated. What is missing is the model-derived positive uniform `kappa`.

---

# 4. Complete continuous-vacuum one-link Harnack — PR #3894

PR #3894 introduced the complete direct ground-state one-link weight built from the canonical continuous physical-vacuum representative.

Schematically,

```text
W_c(g)
  = ||T||^{-1}
    * Omega_c(left)
    * K(left, right[target <- g])
    * Omega_c(right[target <- g]).
```

The canonical theorem gives strict positivity and the pairwise volume-independent Harnack estimate

```text
W_c(g) <= exp(16 beta) * W_c(h).
```

The factor is the product of the raw-kernel and continuous-vacuum Harnack factors. The proof is division-free and does not evaluate an arbitrary `L²` representative pointwise.

---

# 5. Sharp normalization and Doeblin comparison — PR #3898

Let

```text
mu = normalized compact Haar on SU(N)
Z  = integral W_c dmu
rho(g) = W_c(g) / Z
nu = rho * mu.
```

Instead of introducing an anchored lower/upper bound and paying the Harnack factor twice, the proof integrates the pairwise Harnack inequality directly.

With

```text
R = exp(16 beta),
```

the canonical result is

```text
0 < Z < infinity
R^{-1} <= rho(g) <= R
R^{-1} mu <= nu <= R mu.
```

Thus the normalized one-link law has a volume-independent Doeblin comparison with a **single** `exp(16 beta)` factor. No `exp(32 beta)` loss is introduced.

---

# 6. Sharp normalized one-link variance — PR #3907

The normalized measure comparison is consumed directly at the centered-variance layer.

For `L²` observables on the one-link group, the canonical route proves the corresponding lower variance comparison

```text
R^{-1} * evariance_mu(X) <= evariance_nu(X),

R = exp(16 beta).
```

Equivalently, the sharp coefficient is `exp(-16 beta)`.

This step also transports the required `L²` membership from Haar to the normalized one-link law using the upper measure comparison. Again, the Harnack factor is paid once rather than squared.

This is the current quantitative local input to the block-dynamics program.

---

# 7. A.e. bridge to the actual ground-state joint fiber — PR #3909

The direct continuous-vacuum law and the legacy ground-state joint density do not use the same pointwise representative of the vacuum. The correct bridge is therefore almost-everywhere, not pointwise.

The canonical theorem now:

```text
reconstructs a complete right boundary from retained off-target coordinates;
uses Omega_c = Omega almost everywhere under spatial-slice Haar;
transports that equality through the exact target/off-target Haar split;
identifies the legacy normalized split target fiber with the continuous law
  for Haar-a.e. left boundary and Haar-a.e. retained off-target context;
proves exact singleton-target Measure.map transport back to SU(N).
```

Hence, after target-coordinate evaluation, the actual ground-state split one-link fiber agrees almost everywhere with the sharp continuous-vacuum direct normalized law.

The exceptional contexts remain explicit. This theorem does **not** claim an RCD identification or promote an arbitrary quotient representative to a pointwise function.

---

# 8. Present mathematical frontier

The next step is now much more specific than the old "prove a twelve-color Poincaré inequality" formulation.

The immediate task is to **consume the new a.e. fiber compatibility theorem inside the actual ground-state conditional-expectation hierarchy**. In concrete terms:

```text
sharp direct one-link variance
  + a.e. equality of actual split fibers
  -> sharp variance lower bound for the genuine joint one-link update
  -> color-block conditional variance / residual estimate
  -> six-right and six-left block Dirichlet control
  -> twelve-block coercivity on the complement of its common-fixed sector.
```

Only after this bridge is formalized should the proof attempt a global Poincaré coefficient.

The decisive quantitative milestone is still

```text
exists kappa_* > 0, for every relevant scale n,
  kappa_* * ||z||^2 <= E12_n(z)
```

on the correct common-fixed-space orthogonal complement, with `kappa_*` derived from the actual Wilson / ground-state model.

If such a coefficient is established, the already-integrated route gives

```text
uniform physical transfer gap >= 3 kappa_* / 4.
```

---

# 9. What is still not proved

The following remain open unless and until an explicit theorem discharges them:

```text
one-link a.e. fiber compatibility
  != global block conditional-expectation coercivity

positive finite-scale block coefficient
  != scale-independent coefficient

local Harnack / Doeblin / variance control
  != global L² Poincaré theorem

qualitative common-fixed characterization
  != identification with the final physical vacuum sector

fixed finite-volume physical gap
  != continuum mass gap

same-root scalar continuum process
  != full 4D continuum Yang--Mills field

one selected positive exact mode
  != global spectral floor
```

---

# 10. Current priority

The preferred proof order is now:

```text
1. transfer the exp(-16 beta) one-link variance bound through the
   #3909 a.e. joint-fiber compatibility theorem;
2. formulate and prove the corresponding genuine one-link conditional-
   expectation residual inequality on the ground-state joint carrier;
3. aggregate one-link residuals to spatial color blocks;
4. assemble the right-six and left-six block dynamics;
5. identify the exact common-fixed sector relevant to physical
   top-orthogonal right-boundary lifts;
6. prove a positive scale-independent twelve-block Poincaré coefficient;
7. invoke the integrated E12 -> E6 -> raw defect -> transfer-gap route;
8. propagate the resulting uniform gap to the same-root thermodynamic /
   continuum physical construction.
```

This is the present constructive frontier of MGAP4D.

---

## Navigation

- `ROADMAP.md` — ordered proof program and completion criteria.
- `MGAP4D/MathlibAnalytic/` — Lean/mathlib theorem development.
- `docs/` — supporting bridge and review documentation.
- `EXTERNAL_REVIEW_CHECKLIST.md` — carrier / claim-boundary review checklist.

CI-green Lean proofs are proof artifacts, but the repository continues to distinguish fixed-finite-volume theorem closure from the unresolved physical continuum boundary.
