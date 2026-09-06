# MGAP4D Roadmap

This roadmap records the current proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-06 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the mathematical checkpoint represented by this document is

```text
0d947530acc81c4d0fe05aeada6dba390d6cda78
```

which is the normal merge of PR #3507,

```text
Add finite-volume physical pair relative Poincare estimate.
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as current proof status.

> **Current frontier**
>
> The fixed-finite-volume physical-pair program has now reached a genuine Poincaré/Green endpoint. The canonical branch contains the completed top/non-top decomposition, strict non-top contraction, arbitrary-power decay, strong convergence to the full top projection, fixed-space characterization, non-top coercivity, real spectral confinement, quantitative resolvent estimates, a Green operator, exact reduced-range identification, and a relative Poincaré inequality.
>
> Therefore the next global mass-gap problem is **not** to invent another fixed-volume coercive theorem. It is to determine whether the finite-volume residual factor `1 - ‖R‖` can be controlled uniformly along the physically relevant scaling family, or whether a stronger model-derived quantity is required.
>
> In parallel, the SU(2) exact-mode lane has pushed its remaining model input upstream to a realizable one-step raw-Wilson-kernel limit plus explicit finite/common-time coherence.
>
> Neither lane yet proves top-sector simplicity, vacuum uniqueness, a thermodynamic/continuum global spectral gap, or the full four-dimensional Yang--Mills field required for a Clay-level theorem.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated implication machinery** — theorem chain is formalized, but a model-facing input remains.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Diagnostic only** — correct theorem/obstruction that is not the active gap mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                        [Integrated]
  -> reflection positivity / boundary geometry                      [Integrated]
  -> physical spatial-slice transfer                                [Integrated]
  -> completed physical pair carrier                                [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                         [Integrated]
  -> rational/continuum scalar law                                  [Integrated]
  -> continuum OS positivity                                        [Integrated]
  -> direct-limit Hilbert carrier                                   [Integrated]
  -> real C₀ semigroup                                              [Integrated]
  -> graph-closed self-adjoint Hamiltonian                          [Integrated]
  -> vacuum Ω / complete Ω⊥                                         [Integrated]

C. FINITE PHYSICAL-PAIR GEOMETRY

one-slice F ⊕ Fᗮ                                                   [Integrated]
  -> four pair blocks                                               [Integrated]
  -> completed TT / NN decomposition inside PP                      [Integrated]
  -> NN = PP ⊓ TTᗮ                                                 [Integrated]

D. FINITE NON-TOP DYNAMICS

q = ‖R‖ < 1                                                        [Integrated]
  -> ‖SN‖ ≤ q                                                       [Integrated]
  -> q^k decay                                                      [Integrated]
  -> S₂^k -> P_TT strongly on PP                                   [Integrated]
  -> Fix(S₂ | PP) = TT                                              [Integrated]

E. FINITE COERCIVE / SPECTRAL / GREEN THEORY

(1-q)‖x‖ ≤ ‖x-SN x‖                                                [Integrated]
  -> real point-spectrum exclusion                                  [Integrated]
  -> spectrum ℝ SN ⊆ [-q,q]                                        [Integrated]
  -> quantitative real resolvent                                    [Integrated]
  -> G=(I-SN)⁻¹ with ‖G‖≤(1-q)⁻¹                                  [Integrated]
  -> range(I-S₂ | PP)=NN                                            [Integrated]
  -> relative Poincaré estimate                                     [Integrated]

F. GLOBAL GAP LANE

finite-volume 1-q(H,N,β) > 0
  -> model-derived scale-uniform lower bound                         [OPEN NOW]
       OR prove degeneration and replace the controlling quantity    [OPEN NOW]
  -> uniform Green/Poincaré control                                  [OPEN DOWNSTREAM]
  -> thermodynamic/scaling-limit propagation                         [OPEN DOWNSTREAM]
  -> global continuum spectral lower bound                           [OPEN DOWNSTREAM]

G. SU(2) EXACT-MODE LANE

selected physical/top endpoint pair                                 [Integrated]
  -> literal raw one-slab kernel coefficient                        [Integrated]
  -> realizable one-step raw-kernel limit/coherence                  [OPEN NOW]
  -> selected completed-boundary weak identity                       [generated downstream]
  -> exact common-carrier mode                                       [Integrated implication machinery]
  -> Ω⊥ Hamiltonian mode at exactGapValueReal                        [Integrated implication machinery]

H. FULL CLAY-LEVEL COMPLETION

selected scalar continuum != full 4D gauge field                     [OPEN]
relative top block != unique vacuum line                              [OPEN]
full same-root OS/Wightman physical carrier                           [OPEN]
positive spectrum above the vacuum                                   [OPEN]
Clay-level existence + mass gap                                      [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

Repository-operation rules for theorem work:

```text
start from the exact authoritative canonical SHA
use GitHub-mediated repository operations
accept CI only when workflow/job/Lean step are terminal success
never treat queued or in_progress as success
write-freeze while exact-head CI is running
inspect terminal failure logs before editing
keep proof development additive/tighten-only
forbid sorry / admit / axiom / placeholder declarations
fresh-check exact head/base/mergeability/reviews/threads before merge
normal-merge with expected head SHA fixed
verify merge parents and canonical branch pointer
verify post-merge canonical CI and trusted cache
```

Claim discipline:

```text
finite theorem != continuum theorem
q_n < 1 for every n != inf_n (1-q_n) > 0
relative distance to TT != distance to a unique vacuum line
one positive exact mode != global spectral floor
same-root scalar continuum != full 4D Yang--Mills field
real finite-volume resolvent != complex/continuum resolvent
conditional bridge machinery != discharged raw-model input
```

Current authoritative CI at this checkpoint uses Lean `4.30.0-rc2` and Lake `5.0.0-src+3dc1a08`.

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the actual periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include:

```text
oriented lattice / edge / plaquette geometry
normalized Haar probability structure
Wilson action / Gibbs density / probability measure
reflection-fixed geometry and positive-time decomposition
finite Wilson reflection positivity
boundary and spatial-slice coordinate systems
gauge-covariant holonomy
gauge-invariant normalized trace observables
integer temporal translation / reflection covariance
finite support geometry
```

Permanent rule: keep the interacting Wilson model visible through every decisive physical bridge.

---

# Phase 2 — Same-root primary scalar continuum law

**Status: Integrated.**

Integrated route:

```text
finite primary gauge-invariant scalar readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum probability law
```

This is a same-root continuum observable process, not yet the complete gauge field on `ℝ⁴`.

---

# Phase 3 — Continuum OS Hilbert reconstruction and Hamiltonian

**Status: Integrated.**

Integrated chain:

```text
continuum rational-cylinder OS positivity
continuum reflection invariance
OS null quotient
fixed-slot real Hilbert completions
isometric directed system
completed direct-limit carrier
NNReal strongly continuous contraction semigroup
right generator / right Hamiltonian
graph closure as Mathlib LinearPMap
self-adjoint graph-closed Hamiltonian
resolvent / Yosida recovery
normalized vacuum Ω
complete vacuum-orthogonal sector Ω⊥
```

This phase is not the immediate blocker.

---

# Phase 4 — Transfer spectral / logarithmic-generator / Wightman lane

**Status: Integrated analytic machinery; model realization remains relevant.**

Canonical machinery includes:

```text
positive compact transfer spectral support
strictly-positive transfer support
partially-defined logarithmic generator
resolvent/effective-energy identities
intrinsic logarithmic spectral floor
spectral-mode eigenvector/domain theorems
canonical spectral span as a Mathlib operator core
common-core Hilbert equivalence machinery
self-adjoint maximality / closure transfer
transfer point-energy <-> target Hamiltonian point-energy implications
attained mass-gap certificate implications
```

The remaining physical question is not the abstract operator theory; it is whether the required model-facing realization data can be proved on the final same-root carrier.

---

# Phase 5 — SU(2) selected exact-mode lane

**Status: Integrated implication machinery; raw-model input remains open.**

The older selected-mode seam has been tightened substantially beyond PR #3151.

Key reductions include:

```text
selected physical mode + normalized top mode
  -> arbitrary pair-Haar weak matrix coefficient
  -> literal one-slab Wilson Hilbert-Schmidt kernel coefficient
  -> projected synthesis approximation
  -> realizable integer one-step raw-kernel limit property
  -> theorem-generated selected completed-boundary weak identity
```

By PR #3177, the remaining exact-mode model seam is concentrated in:

```text
1. a finite raw one-step kernel limit statement; and
2. explicit common/realizable one-step time coherence.
```

Downstream wrappers already generate the exact common-carrier mode and graph-closed Hamiltonian mode once those finite inputs are supplied.

### Completion criterion

Do **not** assume the finite OS eigen-equation or the final Hamiltonian eigen-equation. Prove the remaining raw-kernel limit/coherence directly from the finite Wilson model and its translation/synthesis machinery.

---

# Phase 6 — Physical pair carrier geometry

**Status: Integrated.**

This phase is the major development added after the older roadmap checkpoint.

Let

```text
F = full eigenvalue-one subspace of normalized one-slice physical transfer
K = Fᗮ
PP = completed physical pair carrier generated by decomposable physical pairs
TT = completed top-top block from F ⊠ F
NN = completed sum/closure of blocks carrying at least one K factor
```

The integrated progression is:

```text
#3436  decomposable four-block orthogonality
#3438  lift orthogonality to generated spans
#3440  lift orthogonality through Hilbert closure
#3442  prove one-slice F ⊕ K decomposition
#3445  decompose physical pair generators into four blocks
#3448  complete the physical pair orthogonal decomposition
```

The resulting geometry is relative to `PP`:

```text
TT ⟂ NN
PP = completed top/non-top orthogonal sum
NN = PP ⊓ TTᗮ
```

### Permanent claim boundary

Do not replace the last identity by ambient

```text
NN = TTᗮ
```

unless an independent theorem proves that `PP` is the full ambient pair-Haar carrier.

No such ambient equality is currently claimed.

---

# Phase 7 — Strict non-top contraction and arbitrary-power decay

**Status: Integrated.**

Let

```text
R  = one-slice orthogonal transfer restriction
q  = ‖R‖
S₂ = normalized physical pair transfer
SN = restriction of S₂ to NN
```

Integrated milestones:

```text
#3457  obtain K⊠F / F⊠K bounds by q and K⊠K by q²
#3470  lift to completed non-top contraction: ‖SN‖ ≤ q < 1
#3474  prove arbitrary-power bound ‖SN^k x‖ ≤ q^k ‖x‖
#3477  prove quantitative convergence S₂^k x -> P_TT x on PP
```

The central finite-volume estimate is:

```text
‖S₂^k x - P_TT x‖ ≤ q^k ‖P_(TTᗮ) x‖,
```

for `x ∈ PP`.

This is strong convergence to the **full top-top projection**.

---

# Phase 8 — Fixed space, coercivity, and real spectral confinement

**Status: Integrated.**

Integrated milestones:

```text
#3480  S₂ x = x <-> x ∈ TT for x ∈ PP
#3482  (1-q)‖x‖ ≤ ‖x-SN x‖ and ker(I-SN)=⊥
#3485  exclude nonzero real eigenvectors with |λ|>q
#3487  spectrum ℝ SN ⊆ [-q,q] ⊂ (-1,1)
#3495  ‖resolvent SN λ‖ ≤ (|λ|-q)⁻¹ for q<|λ|
```

### Mathematical meaning

At every fixed finite volume, the completed non-top sector is spectrally separated from real unit eigenvalues and has explicit resolvent control.

### Claim boundary

This is not yet a scale-uniform gap. The quantity `q=q(H,N,β)` depends on finite-volume/model data.

---

# Phase 9 — Green operator, exact reduced range, and relative Poincaré estimate

**Status: Integrated.**

This is the current completed finite-volume endpoint.

Integrated milestones:

```text
#3501  define G = resolvent SN 1 = (I-SN)⁻¹ on NN
       prove two-sided inverse identities
       prove ‖G‖ ≤ (1-q)⁻¹
       prove unique non-top Poisson solutions

#3503  prove residuals of PP lie in NN
       prove every n∈NN has a unique reduced preimage
       prove range(I-S₂ | PP) = NN
       prove NN = PP ⊓ TTᗮ

#3507  prove the relative finite-volume Poincaré estimate
```

The final finite-volume inequality is:

```text
(1-q) ‖P_(TTᗮ) x‖ ≤ ‖x-S₂x‖,
```

for every `x ∈ PP`, with inverse-factor form

```text
‖P_(TTᗮ) x‖ ≤ (1-q)⁻¹ ‖x-S₂x‖.
```

Equivalent formulations control the distance from `x` to `P_TT x`.

### Completion assessment

The fixed-volume Poincaré problem is now **closed at the relative top-sector level**. Further abstract reformulations of the same fixed-volume inequality are lower priority than the scale-uniform problem below.

---

# Phase 10 — Derive a scale-uniform gap quantity from the raw model

**Status: OPEN NOW — highest-priority global-gap frontier.**

The current theorem chain gives, for each fixed cutoff/model parameter set,

```text
0 < 1 - q_n.
```

This is insufficient for a continuum mass-gap theorem unless the positive control survives the approximating/scaling family.

The next mathematical unit must therefore determine whether one can prove

```text
inf_n (1 - q_n) > 0
```

for the physically relevant family.

### Required proof discipline

The uniform estimate must be **derived from the actual model**. Do not introduce a new hypothesis of the form

```text
assume ∃δ>0, ∀n, 1-q_n≥δ
```

merely to unlock downstream machinery.

### Two acceptable outcomes

#### Route A — uniform contraction succeeds

Prove a raw-model theorem giving

```text
q_n ≤ q_* < 1
```

uniformly over the approximating family.

Then immediately specialize the already-integrated finite theorems to obtain:

```text
uniform q_*^k decay
uniform coercivity
uniform real resolvent bounds
uniform Green bounds
uniform relative Poincaré estimates
```

#### Route B — the norm factor degenerates

If the actual model proves `q_n -> 1` or otherwise prevents a useful uniform bound, formalize that obstruction and identify a stronger coercive quantity, decomposition, multiscale estimate, or block transfer whose lower bound can remain uniform.

This is a mathematically valid outcome and is preferable to hiding the degeneration behind an assumption.

### Completion criterion

A theorem stated entirely in model-derived finite data supplies a positive scale-independent constant, or proves why the present `q_n` mechanism cannot do so and replaces it by a better model-derived quantity.

---

# Phase 11 — Uniform finite-volume Green/Poincaré package

**Status: OPEN DOWNSTREAM; theorem infrastructure mostly available.**

Once Phase 10 supplies a genuine uniform constant `δ>0`, package the finite family so that for every cutoff:

```text
δ ‖P_(TT_nᗮ) x‖ ≤ ‖x-S₂,n x‖
‖G_n‖ ≤ δ⁻¹
‖SN_n^k‖ ≤ (1-δ)^k
```

with all carrier embeddings and normalization maps explicit.

### Required checks

```text
same physical normalization across cutoffs
explicit dependence of H/N/β/lattice spacing
no hidden change of pair carrier
no replacement of relative TT_nᗮ by a vacuum line
```

### Completion criterion

A cutoff-indexed theorem package exposes constants and maps in a form directly usable by the existing common-carrier/OS limit machinery.

---

# Phase 12 — Propagate the uniform estimate to the common continuum carrier

**Status: OPEN DOWNSTREAM.**

The next step after uniform finite control is not merely numerical convergence of constants. One must transport the **operators, sectors, and inequalities** through the same-root approximating system.

Targets:

```text
finite PP_n / TT_n / NN_n
  -> compatible common-carrier subspaces

finite S₂,n / SN_n
  -> limiting contraction or semigroup statement

uniform residual coercivity
  -> closed continuum coercive estimate

uniform Green control
  -> stable continuum resolvent/Poisson control where appropriate
```

### Main technical danger

A sequence of finite inequalities is not automatically an inequality on the continuum OS/Wightman physical carrier. Domain convergence, subspace convergence, normalization, and operator convergence must all be explicit.

### Completion criterion

The continuum theorem is obtained from the finite Wilson approximants through proved common-carrier maps, not by restating the finite bound as a continuum hypothesis.

---

# Phase 13 — Decide how the full top sector relates to the vacuum

**Status: OPEN DOWNSTREAM; do not assume simplicity.**

Current finite results use the full `TT` sector and prove

```text
Fix(S₂ | PP) = TT.
```

They do not prove:

```text
dim TT = 1
TT = span{Ω}
vacuum uniqueness
```

A later global mass-gap theorem must therefore take one of two routes:

```text
A. prove top-sector simplicity / vacuum identification from the model;

or

B. formulate and transport the spectral gap relative to the full fixed sector,
   then prove separately that this is the physically correct vacuum sector.
```

### Forbidden shortcut

Do not identify `TT` with a vacuum line by notation, finite-dimensional intuition, or downstream physical expectation.

---

# Phase 14 — Finish the SU(2) raw-kernel exact-mode seam

**Status: OPEN NOW in parallel with Phase 10.**

This lane is logically separate from uniform coercivity and may be advanced independently.

The remaining finite-model unit should prove the realizable one-step raw-kernel limit/coherence required by the PR #3177 reduction.

Intended ingredients include:

```text
literal one-slab normalized Wilson kernel
finite temporal translation
Wilson Gibbs translation invariance
positive-time synthesis
boundary/pair isometries
Fubini / Hilbert-Schmidt matrix-coefficient formulas
projected synthesis density
explicit dimensionless/physical time normalization
```

### Completion criterion

The selected SU(2) weak boundary-transfer property is theorem-generated from raw finite Wilson data with no model-facing weak/eigen hypothesis remaining.

### What this would prove

It would close the selected exact-mode realization chain to a positive Hamiltonian mode at `exactGapValueReal` inside the existing implication framework.

### What it still would not prove

```text
that exactGapValueReal is the global spectral floor
that no spectrum lies below the selected mode
vacuum uniqueness
full 4D continuum Yang--Mills existence
```

---

# Phase 15 — Relate the exact-mode and global-coercive lanes

**Status: OPEN DOWNSTREAM.**

Once both lanes are sufficiently model-derived, determine their precise relationship.

Possible outcomes:

```text
1. the uniform relative Poincaré lower bound equals the intrinsic spectral floor;
2. the selected exact SU(2) mode attains that floor;
3. the exact mode lies above a separately proved lower floor;
4. the two lanes live on different intermediate carriers and require an additional identification theorem.
```

Do not declare equality of the two gap values without a Lean theorem connecting them.

### Completion criterion

A theorem on the same final physical carrier identifies the lower-bound quantity, intrinsic spectral floor, and selected exact mode as far as the model actually supports.

---

# Phase 16 — Full four-dimensional same-root Yang--Mills field/state

**Status: OPEN.**

The existing same-root scalar continuum process is not the full field required for the Clay problem.

The final construction must support an appropriately rich four-dimensional gauge-invariant/local observable structure with the necessary combination of:

```text
Euclidean covariance
gauge structure / gauge-invariant local observables
reflection positivity
regularity / distributional control
physical nontriviality
vacuum and clustering structure
OS/Wightman reconstruction on the same model
```

The finite transfer and scalar continuum lanes should be reused rather than bypassed, but the carrier must be rich enough to support the final Yang--Mills statement.

---

# Phase 17 — Final spectral gap above the physical vacuum

**Status: OPEN.**

The final spectral theorem must be stated on the actual reconstructed physical Hamiltonian carrier.

Target shape:

```text
H Ω = 0
‖Ω‖ = 1
spec(H | Ω⊥) ⊆ [m,∞)
0 < m
```

or an equivalent rigorous formulation compatible with the final carrier and vacuum structure.

Every identification used here must be model-derived:

```text
finite transfer -> common carrier
common carrier -> final OS/Wightman carrier
top/fixed sector -> physical vacuum sector
finite or exact-mode energy -> final Hamiltonian spectrum
```

---

# Phase 18 — Clay-level theorem and release boundary

**Status: OPEN.**

Only after the previous phases are discharged should the repository claim a completed Yang--Mills existence-and-mass-gap theorem.

Required final audit:

```text
no unresolved model-facing hypotheses
no hidden scale-uniform assumptions
no finite/continuum carrier substitution
no selected-mode/global-floor conflation
no top-sector/vacuum-line conflation
no symbolic/numerical exact-gap conflation
no sorry / admit / axiom / placeholder declaration
all decisive bridges on the same physical construction
```

---

# Diagnostic lane — finite Dobrushin covariance

**Status: Diagnostic only.**

The finite high-temperature covariance theorem remains correct, but its active majorant

```text
q_D(β) = (exp(4β)-1)/(exp(4β)+1)
```

satisfies

```text
q_D(β) -> 1
```

as `β -> +∞`, with the corresponding simple geometric factor failing to stay `<1` in the desired scaling regime.

Therefore this particular Dobrushin mechanism is not the current global continuum mass-gap route.

Its role is useful: it demonstrates exactly why “finite clustering” and “scale-uniform physical gap” must remain separate claims.

---

# Near-term ordered work

The preferred next mathematical units are:

```text
1. Analyze q(H,N,β) along the intended scaling family.
   Prove a genuine uniform lower bound for 1-q, or formalize its degeneration.

2. If uniformity succeeds, package cutoff-uniform decay/coercivity/resolvent/Green/Poincaré estimates.
   If it fails, replace q by a stronger model-derived coercive mechanism.

3. In parallel, close the PR #3177 realizable raw-kernel limit/time-coherence seam for the selected SU(2) exact mode.

4. Transport the successful global finite estimate through the actual common-carrier/OS limit maps.

5. Resolve the relation between the full fixed/top sector and the physical vacuum sector without assuming simplicity.

6. Compare the global lower-bound lane with the selected exact-mode/intrinsic spectral-floor lane on one final carrier.

7. Enlarge the same-root continuum construction to the full four-dimensional Yang--Mills field/state required by the final theorem.
```

The guiding principle is now clear: **the fixed-finite-volume Hilbert analysis is strong enough that the main mathematical risk has shifted to uniformity, scaling, and physical-carrier identification.** The roadmap should stay focused there rather than accumulating equivalent finite-volume reformulations.
