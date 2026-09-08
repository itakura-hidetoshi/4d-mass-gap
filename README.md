# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, transfer operators, and the mass-gap problem.

The repository is deliberately strict about theorem provenance and claim boundaries. It distinguishes:

1. statements proved from the actual finite periodic compact `SU(N)` Wilson model;
2. same-root continuum / OS / Hamiltonian constructions built from finite Wilson observables;
3. finite-volume physical transfer and spectral theorems;
4. model-facing ground-state conditional-expectation / Doob geometry;
5. implication machinery whose hypotheses still require a genuine model-derived quantitative proof; and
6. the remaining steps toward a complete four-dimensional Yang--Mills existence-and-mass-gap theorem.

> **Current claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current development has moved well beyond an abstract finite-volume transfer-gap reduction. The canonical branch now contains an actual ground-state Wilson joint-law route with genuine spatial conditional expectations, exact residual identities, concrete routing to the raw physical one-slab squared defect, and a reduction of the physical transfer-gap problem to a quantitative Poincaré / contraction theorem for the real ground-state conditional-expectation dynamics.
>
> What remains open at the present frontier is not another abstract Hilbert-space gap lemma. The central unresolved analytic/geometric step is to prove a **positive scale-independent Poincaré coefficient for the actual two-sided twelve-spatial ground-state conditional-expectation family**, together with the required common-fixed-space identification, from the Wilson/Doob/Harnack structure itself.

---

## Repository status — 2026-09-09 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

Latest merged canonical checkpoint:
  97945a33d872de268b8f0cd14831f40fb12d733f
  PR #3704
  Reduce six-spatial ground-state frame to mean-projection contraction

Active mathematical PR during this documentation refresh:
  PR #3707
  Route twelve-spatial joint Poincare to the physical transfer gap

Exact green Lean proof head before this docs-only refresh:
  eb8ae2b7e4c07fe266810076a416d4da80f3122a

PR #3707 validation at that proof head:
  PR Lean Fast Check #13406 = completed / success
  Changed Lean fast check = completed / success
  Run changed Lean fast check = completed / success

Public landing branch:
  main

Detailed development order:
  ROADMAP.md
```

Only theorem results merged into `formal/real-hilbert-uniform-coercive-strong-limit` count as authoritative canonical proof status. A green open PR is documented as a validated candidate unit, not as already-merged mathematics.

---

# Proof picture in one view

```text
A. ACTUAL FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L² carriers
  -> normalized one-slab physical transfer
  -> positive / strictly-positive ground-state transfer structure

B. SAME-ROOT CONTINUUM OS LANE

finite Wilson scalar readout
  -> rational-time path law
  -> same-root continuum scalar law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C₀ contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω and complete Ω⊥ sector

C. FINITE PHYSICAL-PAIR LANE

one-slice top eigenspace F and K = Fᗮ
  -> completed physical pair carrier PP = TT ⊕ NN
  -> strict non-top contraction q = ‖R‖ < 1
  -> power decay and strong convergence to P_TT
  -> fixed-space characterization
  -> coercivity / real spectral exclusion / resolvent control
  -> Green operator and exact reduced range
  -> relative finite-volume Poincaré estimate

D. GROUND-STATE WILSON JOINT-LAW LANE

physical ground-state one-slab joint measure Π
  -> left/right boundary L² isometries
  -> Doob boundary geometry
  -> six genuine right spatial condExp projections
  -> six genuine left spatial condExp projections
  -> two-sided twelve-spatial family on one joint L² carrier
  -> concrete eight-color family = six spatial + two temporal identities
  -> exact residual-to-raw-physical-defect comparison at η = 1

E. CURRENT QUANTITATIVE GAP REDUCTION

actual six-spatial residual E₆
  = ‖u‖² - (1/6) Σ_c ‖P_c R u‖²

mean-projection contraction q < 1
  -> six-spatial frame κ = 1-q
  -> physical top-eigenspace transfer gap >= 3(1-q)/8

actual two-sided twelve-spatial residual E₁₂                 [PR #3707 green]
  = 1/2 (E₆,right + E₆,left)

on right-boundary lifts:
  E₁₂(Ru) = 1/2 E₆(u)                                       [PR #3707 green]

12-color Poincaré κ
  -> six-spatial frame 2κ
  -> physical transfer gap >= 3κ/4                          [PR #3707 green]

F. PRESENT OPEN FRONTIER

identify the common-fixed space of the actual 12 condExp projections          [OPEN]
  + prove a positive scale-independent 12-color joint Poincaré coefficient   [OPEN]
  from genuine Wilson / Doob / Harnack geometry                               [OPEN]
  -> scale-uniform physical transfer gap                                      [DOWNSTREAM]
  -> stable thermodynamic / continuum propagation                             [DOWNSTREAM]
  -> full physical continuum spectral gap                                     [DOWNSTREAM]

G. CLAY-LEVEL COMPLETION

full same-root 4D continuum Yang--Mills field/state                            [OPEN]
vacuum structure / uniqueness as required                                     [OPEN]
OS/Wightman identification on the actual physical carrier                      [OPEN]
strictly positive spectrum above the vacuum                                    [OPEN]
Clay-level existence + mass gap                                                 [OPEN]
```

The important change from the older roadmap is that the active model-facing problem is no longer merely

```text
find a uniform lower bound for 1 - ‖R‖
```

in an abstract finite-pair theorem. The proof has been pushed upstream into the actual Wilson ground-state law. The present target is a quantitative theorem for the genuine conditional-expectation dynamics themselves.

---

# 1. Actual finite periodic compact `SU(N)` Wilson root

The finite model is built from

```lean
Matrix.specialUnitaryGroup (Fin N) ℂ
```

with normalized Haar probability structure and an interacting periodic-even Wilson Gibbs law.

Canonical finite-model infrastructure includes:

```text
oriented periodic lattice / edge / plaquette geometry
Wilson action and Gibbs probability measure
reflection geometry and positive-time decomposition
finite Wilson reflection positivity / Gram identities
gauge covariance of plaquette holonomy
gauge invariance of normalized trace observables
integer temporal translation and reflection covariance
spatial-slice Haar-L² carriers
boundary Haar-L² carriers
one-slab Wilson kernels
normalized physical transfer operators
```

The interacting Wilson law is never silently replaced by a product Haar law at nonzero coupling.

---

# 2. Same-root scalar continuum OS construction

The repository contains a constructive scalar continuum OS lane obtained from actual finite Wilson pushforwards.

Integrated structure includes:

```text
primary gauge-invariant scalar Wilson readout
reflection-completed rational-time paths
tightness / Prokhorov subsequential continuum law
continuum rational-cylinder reflection positivity
continuum reflection invariance
OS seminorm and null quotient
fixed-slot real Hilbert completions
directed-limit Hilbert carrier
real strongly continuous contraction semigroup
right generator and graph closure
self-adjoint graph-closed OS Hamiltonian
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This is a genuine same-root continuum observable process. It is **not** yet the complete four-dimensional continuum gauge field on `ℝ⁴`.

---

# 3. Transfer / spectral / logarithmic-generator machinery

The canonical branch contains substantial operator-theoretic infrastructure around positive transfer operators and their generators:

```text
compact positive transfer spectral support
strictly-positive spectral support lane
partially-defined logarithmic generator
resolvent and effective-energy identities
intrinsic logarithmic spectral floor
spectral-mode operator core
common-core / self-adjoint intertwining machinery
transfer point energies <-> target Hamiltonian point energies
mass-gap certificate implication machinery
```

This machinery makes downstream implications precise, but it does not manufacture the missing model-derived uniform coercivity.

---

# 4. Completed finite-volume physical-pair theory

At fixed finite-volume data `(H,N,β)`, let schematically

```text
F   = full eigenvalue-one subspace of the normalized one-slice physical transfer
K   = Fᗮ
PP  = completed physical pair carrier
TT  = completed top-top block
NN  = completed non-top block inside PP
R   = one-slice orthogonal transfer restriction
q   = ‖R‖
S₂  = normalized physical pair transfer
SN  = completed restriction of S₂ to NN
```

The canonical branch proves, without assuming one-dimensionality of `F` or `TT`:

```text
TT ⟂ NN
PP = TT ⊕ NN
NN = PP ⊓ TTᗮ
q = ‖R‖ < 1
‖SN‖ ≤ q
‖SN^k x‖ ≤ q^k ‖x‖
S₂^k x -> P_TT x
Fix(S₂ | PP) = TT
(1-q)‖x‖ ≤ ‖x-SN x‖
spectrum ℝ SN ⊆ [-q,q]
‖resolvent SN λ‖ ≤ (|λ|-q)⁻¹  for q < |λ|
G=(I-SN)⁻¹ with ‖G‖ ≤ (1-q)⁻¹
range(I-S₂ | PP)=NN
(1-q) ‖P_(TTᗮ)x‖ ≤ ‖x-S₂x‖
```

These are genuine fixed-finite-volume results. They remain important, but they are no longer the sharpest description of the active model-facing gap frontier.

---

# 5. Ground-state Wilson joint measure and Doob geometry

The newer proof route works on the actual one-slab ground-state joint law rather than replacing it by an abstract family of projections.

The canonical spine now contains:

```text
ground-state one-slab joint probability measure Π
left-boundary and right-boundary L² isometries
ground-state coarse conditional expectation
Doob boundary operator / normalization geometry
strictly positive physical vacuum structure
Wilson marginal / joint-law comparison theorems
```

A decisive design rule is carrier safety: the ground-state joint `L²` route is kept distinct from unrelated global Gibbs `L²` carriers unless an explicit theorem identifies them.

---

# 6. Genuine six + six spatial conditional expectations

On the same ground-state joint `L²` carrier the repository now has twelve genuine spatial conditional expectations:

```text
P₀,...,P₅   = six right-boundary spatial-color conditional expectations
L₀,...,L₅   = six left-boundary spatial-color conditional expectations
```

Each is a real Hilbert-space orthogonal projection, formalized through `condExpL2`, with:

```text
P_c² = P_c
L_c² = L_c
P_c symmetric
L_c symmetric
```

They are packaged as an explicit two-sided twelve-spatial family

```text
P₁₂ : Sum (Fin 6) (Fin 6) -> J ->L[ℝ] J.
```

The fixed-space geometry is already exposed qualitatively:

```text
z fixed by all 12
  <->
(z fixed by all right 6) and (z fixed by all left 6).
```

Moreover every right-boundary lift is fixed by all six left updates. This exact left/right asymmetry is what makes the twelve-color Poincaré route useful for the physical right-boundary sector.

---

# 7. Concrete eight-color physical defect route

The earlier abstract bounded-color family has been removed from the model-facing endpoint.

The physical eight-color family is now literally

```text
six genuine ground-state spatial conditional expectations
+ two identity temporal slots.
```

The two temporal identities contribute zero residual energy, so the eight-color residual reduces exactly to the six-spatial residual.

The canonical route then proves a fully concrete comparison at `η = 1`:

```text
concrete ground-state spatial residual
  -> raw physical one-slab squared defect
  -> normalized top-orthogonal transfer gap.
```

No independent abstract `hcompare` hypothesis is required at this endpoint.

---

# 8. Exact six-spatial Dirichlet / mean-projection identity — canonical through PR #3704

Define the normalized six-spatial residual schematically by

```text
E₆(u) = (1/6) Σ_c ‖R u - P_c R u‖².
```

Because the `P_c` are genuine orthogonal projections, the canonical branch proves the exact identity

```text
E₆(u)
  = ‖u‖² - (1/6) Σ_c ‖P_c R u‖².
```

Thus the six-spatial frame inequality

```text
κ ‖u‖² ≤ E₆(u)
```

is exactly equivalent to contraction of the mean projected squared norm:

```text
(1/6) Σ_c ‖P_c R u‖² ≤ (1-κ) ‖u‖².
```

For the physical top-orthogonal sector, a contraction factor `q ≤ 1` gives

```text
physical transfer gap >= 3(1-q)/8.
```

If `q < 1`, the finite-volume physical transfer gap is strictly positive.

This is now canonical at merge commit

```text
97945a33d872de268b8f0cd14831f40fb12d733f.
```

---

# 9. Two-sided twelve-spatial normalization bridge — PR #3707 green

PR #3707 introduces the conventional `1/12` residual energy of the actual twelve-spatial family:

```text
E₁₂(z) = (1/12) Σ_{c in 12 colors} ‖z - P₁₂,c z‖².
```

At the exact green Lean proof head `eb8ae2b7e4c07fe266810076a416d4da80f3122a`, the PR proves

```text
E₁₂(z) = 1/2 (E₆,right(z) + E₆,left(z)).
```

Because all six left projections fix every right-boundary lift,

```text
E₁₂(Ru) = 1/2 E₆(u).
```

Therefore a conventional twelve-color Poincaré estimate on the physical right-lifted top-orthogonal sector,

```text
κ ‖x‖² ≤ E₁₂(RUx),
```

implies the six-spatial frame estimate

```text
2κ ‖x‖² ≤ E₆(Ux),
```

and hence the explicit physical transfer-gap bound

```text
physical transfer gap >= 3κ/4.
```

The normalization side condition `κ ≤ 1/2` is harmless: any positive coefficient can be reduced to satisfy it.

PR #3707 is green but remains an open Draft during this documentation refresh. The theorem statements in this section therefore describe a validated candidate unit until the PR is normally merged.

---

# 10. Present mathematical frontier

The next serious proof target is now sharply localized.

We need to prove, from the **actual ground-state Wilson joint law**, a scale-independent positive coefficient

```text
∃ κ > 0, ∀ scale n, ∀ physical top-orthogonal x,
  κ ‖x‖² ≤ E₁₂,n(R U x).
```

The mathematically natural route has two coupled parts.

## 10.1 Identify the twelve-color common-fixed space

The repository already knows that common fixedness is equivalent to simultaneous fixedness under the two six-color halves. What remains is to identify that common-fixed sector strongly enough to control the physical right-boundary top-orthogonal image.

The desired geometry is not to assume “constants only” by fiat. It must be proved from the actual sigma-algebras / joint measure / boundary structure.

## 10.2 Derive quantitative Poincaré coercivity

The available one-link Wilson/Doob/Harnack results give genuine local conditional-law control. The remaining task is to assemble those local estimates into a global `L²` coercive bound for the twelve spatial block conditional expectations.

Schematically:

```text
one-link Doob / Harnack variance control
  -> block/color conditional variance control
  -> twelve-color joint Dirichlet form
  -> common-fixed-space orthogonal coercivity
  -> scale-independent κ > 0
  -> physical transfer gap >= 3κ/4.
```

A total-variation or Dobrushin estimate must not be silently promoted to this `L²` Poincaré statement without a theorem supplying the missing step.

---

# 11. Why the two-sided route matters

A direct attempt to prove the six-spatial inequality on the right-boundary lift hides the full Markov geometry. The two-sided joint carrier restores it:

```text
right 6 updates + left 6 updates
```

form a genuine twelve-block conditional-expectation dynamics on one probability space.

On arbitrary joint vectors all twelve blocks are active. On a physical right-boundary lift the left six residuals vanish exactly. Therefore any genuine Poincaré theorem for the full joint dynamics descends to the physical six-spatial frame with a known factor of `2`, rather than through an ad hoc comparison constant.

This is currently the cleanest model-facing route from local Wilson conditional laws to a physical transfer gap.

---

# 12. Dobrushin / Harnack information: useful but not yet the final theorem

The repository contains substantial conditional-law comparison infrastructure, including explicit finite-volume Wilson/Dobrushin and Doob/Harnack estimates.

These results are valuable for:

```text
local variance comparison
strict positivity of conditional densities
quantitative one-link control
diagnostic influence estimates
candidate block-dynamics contraction bounds
```

However, a local bound or a high-temperature Dobrushin contraction is not automatically a scale-uniform continuum mass-gap theorem.

In particular, the simple high-temperature coefficient based on

```text
(exp(4β)-1)/(exp(4β)+1)
```

degenerates as `β -> +∞`, so that mechanism alone cannot be presented as the final continuum gap proof.

---

# 13. SU(2) exact-mode lane remains parallel

The exact-mode lane has pushed its remaining selected-mode input close to the raw Wilson model:

```text
selected physical/top endpoint pair
  -> literal normalized one-slab raw Wilson kernel coefficient
  -> projected synthesis density
  -> realizable one-step raw-kernel limit
  -> explicit finite/common-time coherence
  -> selected completed-boundary weak identity
  -> exact common-carrier mode
  -> graph-closed Ω⊥ Hamiltonian mode at exactGapValueReal.
```

The remaining exact-mode seam is a raw-model one-step limit/coherence theorem.

This lane and the twelve-color Poincaré lane answer different questions:

```text
exact-mode lane:
  realize a selected positive-energy mode

12-color Poincaré lane:
  obtain quantitative control of the whole relevant top-orthogonal sector.
```

Neither is silently substituted for the other.

---

# 14. Top sector is not silently collapsed to a vacuum line

The finite physical-pair theory uses the full top eigenspace and completed top-top block.

The repository does **not** currently claim, merely from the finite-pair results,

```text
dim TT = 1
top eigenspace simplicity
vacuum uniqueness
TT = span{Ω}.
```

Likewise, the current ground-state twelve-color program must identify precisely which common-fixed sector is relevant before translating its Poincaré inequality into a final vacuum-orthogonal continuum statement.

---

# 15. What remains before a Clay-level theorem

A complete theorem still requires one coherent same-root physical construction providing, at minimum,

```text
a sufficiently rich four-dimensional continuum Yang--Mills field/state
Euclidean covariance and gauge-invariant local observable structure
reflection positivity and required regularity/distributional control
physical nontriviality
correct vacuum structure
OS/Wightman identification on the actual physical carrier
a strictly positive spectral gap above the vacuum
```

The current finite Wilson root, same-root scalar continuum process, transfer/OS analytic machinery, exact-mode lane, physical-pair theory, and ground-state conditional-expectation program are substantial components. They are not yet the completed Clay theorem.

---

# 16. Claim discipline

The following implications must not be made silently:

```text
fixed finite-volume gap
  != scale-uniform gap

six/twelve-color conditional expectations at each scale
  != a proved uniform Poincaré coefficient

local Harnack or TV control
  != global L² Poincaré coercivity

relative top-sector control
  != unique-vacuum control

one positive exact mode
  != global spectral floor

same-root scalar continuum process
  != full 4D continuum Yang--Mills field

formal implication machinery
  != discharged model-facing hypothesis

green open PR
  != merged canonical theorem status
```

The repository should always say explicitly which side of each distinction a theorem occupies.

---

# 17. Current priority

The highest-value mathematical task after the present twelve-color normalization bridge is:

```text
1. prove the actual twelve-color common-fixed-space geometry;
2. derive a genuine L² Poincaré / spectral-gap estimate for the twelve-block
   ground-state conditional-expectation dynamics from Wilson/Doob/Harnack data;
3. make its coefficient scale-independent along the physically relevant family;
4. route it through the already-formalized
     E₁₂ -> E₆ -> raw physical defect -> transfer gap
   chain;
5. propagate the resulting uniform physical gap into the thermodynamic /
   continuum OS/Wightman construction without losing the same-root carrier.
```

That is the present constructive frontier of MGAP4D.

---

## Navigation

- `ROADMAP.md` — ordered proof program and completion criteria.
- `MGAP4D/MathlibAnalytic/` — Lean/mathlib analytic development.
- `docs/` — supporting bridge and review documentation.
- `EXTERNAL_REVIEW_CHECKLIST.md` — claim and carrier review checklist.

The project treats CI-green Lean proofs as proof artifacts, but still separates finite-volume theorem closure from the unresolved physical continuum boundary.