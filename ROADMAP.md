# MGAP4D Roadmap

This roadmap records the proof-development order of `itakura-hidetoshi/4d-mass-gap` as of **2026-09-04 JST**.

The authoritative theorem carrier is

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

and the canonical exact checkpoint represented here is

```text
e607fa92e169b47c16a240c0774bfc574a2c601e
```

which is the normal merge of PR #3368,

```text
Bound pair transfer spectra by the unit interval.
```

The public `main` branch is a landing surface. Only theorem results merged into the authoritative theorem carrier count as current proof status.

> **Current frontier**
>
> The finite raw-path / Markov / Fubini seam that dominated the 2026-09-03 public roadmap has now been developed through an actual physical-transfer-power identity, boundary-`L²` realization, an ambient pair-Haar one-slab transfer, and a fixed-ambient recursive transfer semigroup.
>
> The latest merged layer is quantitative and spectral: `T_pair` is contractive and self-adjoint, every finite power is contractive and self-adjoint, its Rayleigh quotients lie in `[-1,1]`, and its real spectrum lies in `[-1,1]`.
>
> The immediate gap-relevant task is no longer to expose the first slab. It is to identify the physically relevant top/vacuum sector and prove a **strict** model-derived contraction or spectral separation on the appropriate complement, then make that bound scale-uniform and transport it through the existing OS/Wightman machinery.
>
> This does **not** mean the Clay Millennium problem is solved. No strict global gap below the top pair-transfer spectral value is claimed here, the current same-root continuum process is still only a selected scalar process, and the full four-dimensional Yang--Mills continuum carrier remains open.

---

## Status legend

- **Integrated** — theorem/model result is merged on the authoritative branch.
- **Integrated implication machinery** — the theorem chain is formalized, but a model-facing or scale-uniform input remains.
- **Open now** — immediate constructive frontier.
- **Open downstream** — required after the current frontier.
- **Diagnostic only** — correct theorem or obstruction that is not the active mass-gap mechanism.

---

# Roadmap in one view

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model                       [Integrated]
  -> reflection positivity / OS boundary geometry                   [Integrated]
  -> boundary and spatial-slice Haar-L² carriers                    [Integrated]
  -> literal one-slab and full-path Wilson kernels                  [Integrated]

B. SAME-ROOT SCALAR CONTINUUM OS

finite Wilson scalar readout                                        [Integrated]
  -> rational path law / Prokhorov continuum law                    [Integrated]
  -> continuum OS positivity                                        [Integrated]
  -> direct-limit real Hilbert carrier                              [Integrated]
  -> real C₀ contraction semigroup                                  [Integrated]
  -> graph-closed self-adjoint OS Hamiltonian                       [Integrated]
  -> normalized vacuum Ω / complete Ω⊥                             [Integrated]

C. FINITE PATH -> PHYSICAL TRANSFER

temporal-gauge Markov/Fubini decomposition                          [Integrated]
  -> raw one-slab physical transfer coefficients                    [Integrated]
  -> full Wilson path = physical transfer power                     [Integrated]
  -> finite-volume excitation decay package                         [Integrated]
  -> boundary L² / one-sided physical transfer                      [Integrated]

D. AMBIENT PAIR-HAAR TRANSFER

literal endpoint-pair kernel K_pair                                [Integrated]
  -> Hilbert-Schmidt T_pair                                         [Integrated]
  -> outer/inner/deep Haar factorization                            [Integrated]
  -> positive-half path = pair-transfer matrix coefficient          [Integrated]

E. FIXED-AMBIENT RECURSION

hold ambient H fixed, recurse only in inward length R               [Integrated]
  -> recursive kernel / Haar message / measurability                [Integrated]
  -> Ψ_(R+2) = T_pair Ψ_R                                           [Integrated]
  -> Ψ_R = T_pair^(R/2) Ψ_(R mod 2)                                 [Integrated]

F. CURRENT PAIR-TRANSFER SPECTRAL LAYER

‖T_pair‖ ≤ 1                                                        [Integrated]
  -> ‖T_pair^k‖ ≤ 1                                                 [Integrated]
  -> T_pair^k self-adjoint                                          [Integrated]
  -> Rayleigh(T_pair^k) ∈ [-1,1]                                   [Integrated]
  -> spectrum_R(T_pair^k) ⊆ [-1,1]                                 [Integrated]

G. NEXT GAP-RELEVANT LAYER

identify top/vacuum sector                                          [OPEN NOW]
  -> model-derived positivity / sharper spectral location if valid  [OPEN NOW]
  -> strict contraction on excitation/vacuum-orthogonal sector      [OPEN NOW]
  -> parity-aware exponential decay of Ψ_R                           [OPEN DOWNSTREAM]
  -> scale-uniform lower bound                                      [OPEN DOWNSTREAM]
  -> OS/Wightman transport                                           [OPEN DOWNSTREAM]

H. FULL PHYSICAL MASS GAP / 4D YM

selected scalar continuum -> sufficiently rich 4D YM field/state   [OPEN]
full same-root physical OS/Wightman carrier                         [OPEN]
strictly positive spectrum above the vacuum                         [OPEN]
Clay-level existence + mass gap                                     [OPEN]
```

---

# Phase 0 — Authority, CI, and claim discipline

**Status: Integrated and permanent.**

The theorem workflow is intentionally conservative:

```text
start from the exact authoritative canonical SHA
accept CI only after workflow / job / exact Lean step are terminal success
never count queued or in_progress as a validation receipt
inspect terminal failures before changing the proof head
keep proof changes additive / tighten-only unless correcting an error
forbid sorry / admit / axiom / placeholder-constant escapes
fresh-check exact base/head/mergeability/reviews/threads before merge
normal merge with expected head SHA pinned
verify merge parent 1 = old canonical
verify merge parent 2 = green proof head
verify the canonical branch points exactly at the merge SHA
```

Permanent claim discipline:

```text
finite theorem != continuum theorem
finite-volume decay != scale-uniform continuum decay
self-adjoint contraction != strict spectral gap
spectrum ⊆ [-1,1] != spectrum ⊆ [0,1]
one positive eigenmode != global spectral gap
selected scalar process != full 4D Yang--Mills field
symbolic exactGapValueReal != a numerical literal without a Lean theorem
```

---

# Phase 1 — Actual finite periodic compact `SU(N)` Wilson model

**Status: Integrated.**

The finite root is the actual periodic-even compact special-unitary Wilson Gibbs model.

Integrated components include:

```text
oriented lattice / edge / plaquette geometry
normalized compact Haar probability structure
Wilson action / Gibbs density / probability measure
reflection-fixed geometry and positive-time decomposition
finite Wilson reflection positivity
boundary and spatial-slice coordinate systems
gauge-covariant holonomy
gauge-invariant normalized trace observables
integer temporal translation / reflection covariance
literal temporal-gauge one-slab and multi-slab kernels
```

Permanent rule: keep the interacting Wilson source visible through decisive bridges. Do not replace the model by an unrelated abstract probability space at the point where a finite Wilson identity must be proved.

---

# Phase 2 — Same-root scalar continuum law and OS Hamiltonian

**Status: Integrated.**

The current constructive continuum lane uses a primary gauge-invariant scalar Wilson readout.

```text
finite primary positive-half readout
  -> reflection-completed rational-time path
  -> scalar path carrier ℚ -> ℝ
  -> tight finite pushforward laws
  -> Prokhorov subsequential continuum law
  -> continuum reflection positivity
  -> OS null quotient and real Hilbert completion
  -> directed-limit carrier
  -> real strongly continuous contraction semigroup
  -> graph-closed self-adjoint OS Hamiltonian
  -> normalized vacuum Ω
  -> complete vacuum-orthogonal sector Ω⊥
```

This is a genuine same-root continuum observable construction. It is not yet the complete four-dimensional gauge field or local observable net.

---

# Phase 3 — Completed physical transfer and spectral implication machinery

**Status: Integrated.**

Before the newer pair-Haar recursion, the repository already contained a substantial completed physical-transfer and spectral lane:

```text
physical spatial-slice gauge-invariant L² carriers
normalized one-slab physical transfer
completed excitation-pair transfer
compact/self-adjoint/positive transfer machinery
strictly-positive spectral support machinery
partial logarithmic transfer generator
resolvent / moment / effective-energy hierarchy
intrinsic logarithmic spectral floor
transfer spectral modes and operator cores
```

The repository also contains transfer/Wightman common-core implication machinery that can propagate suitable same-root finite/continuum spectral inputs to Hamiltonian statements.

This phase provides downstream infrastructure; it does not manufacture the missing scale-uniform model estimate.

---

# Phase 4 — Close the raw finite Markov/Fubini path seam

**Status: Integrated.**

This was the immediate frontier in the previous public roadmap. It is now historical context.

The merged sequence PRs #3213--#3257 establishes, among other results:

```text
PR #3213  finite temporal-gauge Markov/Fubini decomposition
PR #3215  one-slab physical transfer coefficients as raw Haar integrals
PR #3218  first Markov slab lifted to physical transfer
PR #3221  later kernel sections projected to the Gauss-law physical sector
PR #3226  projected two-slab coefficients integrated over the finite tail
PR #3228  specialization to the literal finite Wilson recursion
PR #3231  terminal physical vector carried through the recursion
PR #3234  finite physical recursion = full temporal-gauge path integral
PR #3241  endpoint integrability generated automatically
PR #3246  literal full Wilson path = physical transfer-power coefficient
PR #3249  transfer-normalized literal path inherits excitation decay
PR #3252  raw literal path bound retains the exact top-transfer scale
PR #3255  finite literal-Wilson/spectral-decay package
PR #3257  explicit transport from a rate lower bound to literal Wilson decay
```

Completion consequence: “extract the first adjacent slab from the raw path by Markov/Fubini” is no longer the active frontier.

Remaining limitation: the rate lower bound needed for a continuum mass gap must still be supplied uniformly along the scaling sequence.

---

# Phase 5 — Boundary `L²` and one-sided physical transfer

**Status: Integrated.**

PRs #3260--#3277 move the finite Wilson path identities into the actual OS boundary Hilbert setting:

```text
boundary moments -> inserted positive-half path amplitudes
fixed-boundary unfixed path-kernel representation
automatic shared-boundary L² membership
automatic-analytic boundary-L² gap interface
one-sided physical transfer in ordered endpoint-pair Haar L²
transport to shared reflection-boundary Haar L²
extension to the full Gauss-invariant physical slice
```

No ambient boundary-Hilbert surjectivity is introduced.

---

# Phase 6 — Ambient pair-Haar one-slab transfer and positive-half factorization

**Status: Integrated.**

PR #3279 constructs the literal ordered-pair kernel

```text
K_pair ((A,B),(A',B')) = K(A,A') * K(B,B')
```

and the associated Hilbert-Schmidt operator `T_pair` on pair-Haar `L²`.

PRs #3291--#3322 then provide the finite path-composition layer:

```text
positive-half path kernel = boundary-pair kernel * interior kernel
complete path Haar = boundary pair-Haar × interior Haar
strict interior = inner pair-Haar × deeper Haar in the nondegenerate regime
outer/inner/deep three-factor measure-preserving coordinates
Fubini exposure of all three variables
outer-independent inward message
positive-half path amplitude = pair-transfer matrix coefficient
```

Geometry discipline:

```text
H >= 2 nondegenerate interior pair geometry
H = 1 diagonal central-slice geometry remains separate
```

No false independence is asserted for the coincident central pair.

---

# Phase 7 — Fixed-ambient recursive inward transfer

**Status: Integrated.**

This phase resolves the carrier mismatch that appears if one naively lets the recursion index also control ambient spatial size.

The correct architecture is:

```text
ambient spatial extent H : fixed
remaining inward chain R  : recursive
```

with terminal structure:

```text
R = 0   literal central one-slab terminal
R = 1   diagonal central pair terminal (C,C)
R+2     one pair-kernel peel times the shorter fixed-ambient chain
```

Merged milestones:

```text
PR #3327  fixed-ambient pair peel and product-Haar preservation
PR #3329  fixed-ambient recursive inward chain kernel
PR #3331  recursive Haar message seam
PR #3333  recursive message measurability
PR #3338  exact Markov/Fubini message recursion
PR #3340  common pair-Haar L² recursive messages
PR #3342  Ψ_(R+2) = T_pair Ψ_R
PR #3344  even/odd iteration formulas
PR #3349  Ψ_R = T_pair^(R/2) Ψ_(R mod 2)
PR #3352  Ψ_(R+2k) = T_pair^k Ψ_R
```

This phase gives an exact discrete semigroup normal form on one fixed ambient Hilbert carrier.

---

# Phase 8 — Pair-transfer contraction and recursive-message bounds

**Status: Integrated.**

## PR #3354 — one-step contraction

Using the pointwise Wilson bound and pair-Haar probability structure:

```text
‖K_pair‖_L² ≤ 1
‖T_pair‖ ≤ 1.
```

## PR #3358 — recursive messages

The operator contraction is transported to the fixed-ambient recursion, giving one-pair-step and arbitrary even-step `L²` contraction and a norm bound by the parity terminal message.

## PR #3361 — discrete semigroup power contraction

For every finite `k`:

```text
‖T_pair^k‖ ≤ 1
‖T_pair^k ψ‖ ≤ ‖ψ‖.
```

Completion consequence: the fixed-ambient recursive semigroup has a canonical nonexpansive operator bound at every finite depth.

---

# Phase 9 — Pair-transfer self-adjointness, Rayleigh bounds, and real spectrum

**Status: Integrated through PR #3368.**

## PR #3364 — self-adjointness

Representative symmetry of the literal pair kernel is lifted through the generic symmetric Hilbert-Schmidt-kernel bridge:

```text
T_pair is symmetric
T_pair is self-adjoint
T_pair^k is self-adjoint for every finite k.
```

## PR #3366 — variational contraction

For every vector and every finite power:

```text
|Rayleigh(T_pair^k, ψ)| ≤ 1,
```

so the Rayleigh quotient lies in `[-1,1]`.

## PR #3368 — real spectral location

For every finite `k`:

```text
spectrum ℝ (T_pair ^ k) ⊆ Set.Icc (-1 : ℝ) 1.
```

The proof explicitly handles both subsingleton and nontrivial `Lp` carriers, avoiding an invalid hidden assumption that the operator algebra is automatically nontrivial.

Permanent non-claim at this checkpoint:

```text
self-adjoint + contraction + spectrum ⊆ [-1,1]
does not by itself prove
positivity, spectrum ⊆ [0,1], or a strict gap below 1.
```

---

# Phase 10 — Identify the top/vacuum sector and sharpen the pair spectrum

**Status: OPEN NOW.**

The next gap-relevant step should stay on the actual pair-Haar/Wilson carrier.

Useful targets include:

```text
identify a canonical top/vacuum vector or top spectral subspace for T_pair
prove its invariance/eigenvalue relation from the literal finite model
transport any available kernel positivity to operator positivity, if mathematically valid
sharpen real spectral location only after that positivity is proved
characterize the excitation/vacuum-orthogonal complement
```

Completion criterion for this phase is not a preferred theorem name but a mathematically explicit decomposition of the pair-transfer carrier into its top/vacuum sector and the sector on which a strict contraction can meaningfully be stated.

Forbidden shortcut:

```text
do not infer spectrum ⊆ [0,1] merely from self-adjointness and ‖T_pair‖ ≤ 1.
```

---

# Phase 11 — Prove a strict excitation-sector contraction / spectral separation

**Status: OPEN NOW, after the sector identification.**

The mass-gap-relevant finite target is stronger than nonexpansiveness.

Schematic forms include either

```text
‖T_pair ψ‖ ≤ q ‖ψ‖    with q < 1
```

on the relevant top-orthogonal/excitation sector, or an equivalent spectral statement such as

```text
spectrum(T_pair | excitation sector) ⊆ [-q,q]
```

or, if positivity has first been proved for the exact restricted operator,

```text
spectrum(T_pair | excitation sector) ⊆ [0,q].
```

The constant `q < 1` must come from the model or a proved coercive/Poincaré estimate; it must not be inserted as a hidden assumption and later presented as a derived Wilson theorem.

---

# Phase 12 — Convert strict pair contraction to large-`R` recursive decay

**Status: OPEN DOWNSTREAM; exact semigroup machinery already integrated.**

Once a strict sector contraction is available, the canonical normal form

```text
Ψ_R = T_pair^(R / 2) Ψ_(R % 2)
```

should make the parity-aware decay theorem algebraically direct.

Expected schematic consequence:

```text
‖P_exc Ψ_R‖
  ≤ q^(R / 2) * terminal_norm
```

with the even and odd terminal geometries retained exactly.

This phase must preserve the distinction between

```text
R = 0 one-slab terminal
R = 1 diagonal-central terminal.
```

---

# Phase 13 — Establish scale-uniform control

**Status: OPEN DOWNSTREAM.**

A finite-volume strict contraction is not yet a continuum mass gap. The decisive estimate must survive the scaling sequence.

Possible routes already represented in the repository include:

```text
scale-uniform Poincaré / coercive inequalities
uniform lower bounds on finite excitation decay rates
uniform logarithmic spectral-floor estimates
uniform recursive-message decay
```

The existing finite Dobrushin covariance theorem is not expected to supply this in the large-`β` scaling regime: its active factor tends in the wrong direction (`18 q(β) -> 18`). That lane remains a diagnostic, not the active continuum mechanism.

Completion criterion: a same-root bound with a strictly positive lower spectral scale, or equivalently a strict transfer contraction parameter bounded away from `1`, uniformly along the continuum scaling sequence.

---

# Phase 14 — Transport the uniform finite spectral control through OS/Wightman reconstruction

**Status: OPEN DOWNSTREAM; implication machinery largely integrated.**

The repository already contains substantial common-core and self-adjoint closure machinery for transporting transfer spectral information into Hamiltonian point-energy statements.

The remaining task is to feed that machinery with model-derived, scale-uniform data on the same-root physical carrier rather than an external abstract certificate.

Target shape:

```text
uniform finite transfer separation
  -> continuum OS semigroup decay / spectral lower bound
  -> graph-closed Hamiltonian lower bound on Ω⊥
  -> same-root Wightman spectral statement
```

One selected exact mode may be useful evidence or an attained spectral point, but it is not a substitute for the lower-bound theorem excluding spectrum below it.

---

# Phase 15 — Full four-dimensional Yang--Mills completion

**Status: OPEN DOWNSTREAM.**

The same-root scalar continuum process and the finite/OS transfer machinery are substantial, but a Clay-level result requires a sufficiently rich four-dimensional Yang--Mills theory on one coherent physical carrier.

The final construction must support the required combination of:

```text
Euclidean covariance
gauge-invariant local observable content / gauge structure
reflection positivity
regularity / distributional control
physical nontriviality
vacuum structure and clustering
OS/Wightman reconstruction from the same model
strictly positive spectrum above the vacuum
```

Only after those model and spectral requirements are simultaneously closed is a Clay-level existence-and-mass-gap claim appropriate.

---

# Permanent research rules

The following distinctions should remain visible in future PRs and documentation:

```text
1. Keep ambient H fixed when using the fixed-ambient inward recursion.
2. Keep H=1 diagonal-central geometry separate from independent pair-Haar geometry.
3. Do not turn ‖T‖ ≤ 1 into a strict contraction without a proved q < 1.
4. Do not turn self-adjoint spectrum ⊆ [-1,1] into positivity without a proof.
5. Keep finite-volume, scale-uniform, continuum-OS, and full-Wightman claims separate.
6. Keep one exact mode distinct from a global spectral-floor theorem.
7. Keep the selected scalar continuum process distinct from full 4D Yang--Mills.
8. Preserve exact-SHA CI and merge-parent audit discipline.
```

The immediate mathematical program after the present checkpoint is therefore:

```text
top/vacuum sector
  -> strict excitation-sector spectral separation
  -> fixed-ambient recursive exponential decay
  -> scale-uniform estimate
  -> same-root OS/Wightman mass-gap transport
  -> full 4D Yang--Mills completion.
```
