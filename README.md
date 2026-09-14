# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory, Wilson lattice gauge theory, Osterwalder--Schrader reconstruction, physical transfer operators, ground-state conditional expectations, quantitative mixing, and the mass-gap problem.

The repository is deliberately conservative about claims. It separates exact finite-volume theorems, almost-everywhere bridges, conditional-law identifications, quantitative coercivity inputs, continuum reconstruction, and the final Clay-level target.

> **Claim boundary**
>
> This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.
>
> The current theorem frontier is finite-volume and quantitative. The exact reference one-link conditional law, its off-fiber RCD realization, conditional-variance transport, the C5 continuous-vacuum / local / one-slab-kernel factorization, the quotient-free two-source cross-ratio identity, the explicit source-kernel-difference carrier, and the distinct-source scalar factorization are formalized.
>
> The newest result changes the immediate strategy. For `source != fiber`, the C5 source-kernel difference is a fiber-independent scalar difference times one common base one-slab kernel. Therefore the next theorem is **not** to assume or manufacture exponential distance decay. It is to test whether this scalar cancels exactly after normalization of the literal C5 fiber probability law.
>
> That normalized distinct-source invariance has **not** yet been integrated as a theorem, and no global same-color Dobrushin/coercivity consequence is claimed from it yet.

---

## Repository authority — 2026-09-14 JST

```text
Repository:
  itakura-hidetoshi/4d-mass-gap

Authoritative theorem-carrier branch:
  formal/real-hilbert-uniform-coercive-strong-limit

Fresh exact mathematical theorem baseline observed before this docs refresh:
  ad38daddab638cfc45ac47edd796505527291e78

That commit is the merge of:
  PR #4103
  Factor distinct C5 source change as a scalar

Exact GREEN proof head for #4103:
  c66fd63a13b28365e87ca0dcbc9f8f4afd698d67

Validation receipt:
  PR Lean Fast Check #13811
  workflow run 34809368834
  completed / success

Public landing branch:
  main
```

The authority order is fixed:

```text
1. exact canonical GitHub SHA on the theorem-carrier branch
2. formal Lean artifacts
3. README / ROADMAP
4. CI/runtime receipts
5. historical summaries or memory
```

`main` is a public landing surface, not theorem authority when histories differ. A CI receipt establishes that a particular tree was checked successfully; it is operational evidence, not a substitute for the theorem statement or the exact canonical source tree.

A later docs-only merge may advance the branch pointer beyond the mathematical theorem baseline above. In that case, the docs-only commit is the current branch pointer while `ad38dadd...` remains the theorem-bearing baseline summarized here until a later mathematical merge supersedes it.

---

# Current theorem architecture

```text
A. FINITE WILSON ROOT

periodic-even compact SU(N) Wilson Gibbs model
  -> reflection geometry / Wilson OS positivity
  -> spatial-slice and boundary L2 carriers
  -> physical one-slab transfer and ground-state structure
                                                               [INTEGRATED]

B. SAME-ROOT SCALAR CONTINUUM OS LANE

finite Wilson scalar readout
  -> continuum scalar probability law
  -> continuum reflection positivity
  -> OS Hilbert carrier
  -> real C0 contraction semigroup
  -> self-adjoint OS Hamiltonian / vacuum sector
                                                               [INTEGRATED]

C. FINITE PHYSICAL / GROUND-STATE CONDITIONAL LANE

ground-state one-slab joint probability law
  -> six right + six left genuine spatial condExp projections
  -> twelve-spatial family
  -> E12 -> E6 -> raw physical defect -> transfer-gap routing
                                                               [INTEGRATED ROUTING]

D. SHARP ONE-LINK CONTROL

continuous-vacuum complete one-link weight
  -> exp(16 beta) pairwise Harnack
  -> sharp normalized Haar comparison
  -> exp(-16 beta) one-link variance lower bound
  -> genuine joint condExpL2 residual on bounded core
                                                               [INTEGRATED]

E. CONSTANT REMOTE-INFLUENCE OBSTRUCTION

single-source remote comparison
  -> bounded-test influence
  -> naive constant same-color row majorant
  -> link-count / volume loss
                                                               [OBSTRUCTION INTEGRATED]

F. LOCALITY / COVARIANCE LOCALIZATION

raw same-color Wilson cancellation
  -> source dependence localized
  -> four-integral defect = weighted covariance numerator
  -> target-local x source-local covariance interface
                                                               [INTEGRATED]

G. EXACT REFERENCE ONE-LINK CONDITIONAL LAW

literal normalized one-link fibers
  -> Fubini compatibility
  -> measurable heat-bath kernel / stationarity / idempotence
  -> off-fiber factorization and properness
  -> setwise and integral conditional identities
  -> conditional expectation
  -> condExpKernel / RCD identification
  -> conditional-variance transport
                                                               [INTEGRATED]

H. C5 REFERENCE-FIBER FACTORIZATION

q_A(g) = local(A[fiber <- g]) * K_slab(A[fiber <- g], B[source <- k])
  -> normalize q_A against compact Haar
  -> literal C5 weight = Omega_cont(A[fiber <- g]) * q_A(g)
  -> C5 reference fiber = continuous-vacuum Doob tilt of raw q_A law
                                                               [INTEGRATED]

I. TWO-SOURCE QUOTIENT-FREE INTERFACE

common target weight
  w(g) = Omega_cont(A[fiber <- g]) * local(A[fiber <- g])

source kernels
  K_j(g) = K_slab(A[fiber <- g], B[source <- k_j])

partition / observable integrals
  Z_j = integral w(g) K_j(g) dg
  I_j = integral w(g) f(g) K_j(g) dg

normalized source change
  Z_1 Z_2 (E_1 f - E_2 f)
    = I_1 Z_2 - I_2 Z_1
                                                               [#4094 / #4095 INTEGRATED]

J. EXPLICIT SOURCE-KERNEL DIFFERENCE

I_1 Z_2 - I_2 Z_1
  -> observable change written with K_1 - K_2
  -> mass change written with K_1 - K_2
  -> no source-kernel quotient
  -> target/source/fiber/k_1/k_2 remain explicit
                                                               [#4101 INTEGRATED]

K. DISTINCT-SOURCE SCALAR FACTORIZATION

K_1(g) - K_2(g)
  = (sourceLocalFactor(k_1,g) - sourceLocalFactor(k_2,g))
      * baseKernel(g)

source != fiber
  -> sourceLocalFactor(k,g) independent of g
  -> K_1(g) - K_2(g)
       = (c_1 - c_2) * baseKernel(g)
                                                               [#4103 INTEGRATED]

L. PRESENT FRONTIER: NORMALIZED SCALAR CANCELLATION

individual source update factorization + positivity
  -> identify W_k(g) = c_k * W_base(g) for source != fiber
  -> prove Z_k = c_k * Z_base
  -> cancel c_k exactly in normalized C5 fiber probability
  -> candidate exact equality of distinct-source C5 fiber laws
                                                               [OPEN NOW]

M. BRIDGE BACK TO SAME-COLOR MIXING

if exact normalized distinct-source invariance is proved
  -> identify the exact C5-to-same-color conditional bridge
  -> determine which remote coefficients are literally zero
  -> handle any remaining nonzero incidence cases
  -> obtain a volume-uniform same-color block estimate
                                                               [OPEN NEXT]

N. DOWNSTREAM GAP ROUTE

one same-color block coercivity
  -> six right + six left blocks
  -> quantitative E12 Poincare coefficient
  -> scale-independent kappa_* > 0
  -> physical transfer gap >= 3 kappa_*/4
                                                               [ROUTING PARTLY INTEGRATED]

O. THERMODYNAMIC / CONTINUUM COMPLETION

uniform finite-volume physical gap
  -> thermodynamic / scaling-limit physical carrier
  -> physical OS/Wightman spectral lower bound
  -> sufficiently rich same-root 4D Yang--Mills field/state
  -> Clay-level existence + mass gap
                                                               [OPEN]
```

---

# 1. Exact conditional-law / reference-fiber route

The reference-law disintegration problem is no longer the immediate bottleneck. The canonical theorem chain constructs the literal normalized one-link fiber, proves the required Fubini and conditional identities, builds the measurable heat-bath kernel, factors it through the off-fiber sigma algebra, proves properness, identifies its integral with conditional expectation, identifies the kernel almost everywhere with Mathlib's `condExpKernel`, and transports the relevant conditional variance.

Accordingly, later quantitative arguments may use the proved reference RCD interface. They must not silently generalize it to unrelated fibers or to the full Wilson single-link conditional law.

---

# 2. The C5 raw / continuous-vacuum split

For a selected C5 fiber, the exact source-dependent raw factor is kept as

```text
local x one-slab kernel.
```

The continuous-vacuum factor is separate:

```text
nu_A
  -- Omega_cont Doob tilt -->
mu_ref,A,fiber.
```

Equivalently, the literal C5 fiber weight has the pointwise form

```text
Omega_cont x local x kernel.
```

This distinction is permanent unless a later theorem proves more. In particular,

```text
C5 raw one-slab law != full-4D Wilson singleLinkConditionalMeasure
```

by naming or definition alone.

---

# 3. Quotient-free two-source normalization: #4094 / #4095

The two-source interface preserves the target link, source link, selected fiber, the two source values, the two source-dependent one-slab kernels, and both exact partition functions.

With

```text
w(g)   = Omega_cont(A[fiber <- g]) * local(A[fiber <- g])
K_j(g) = K_slab(A[fiber <- g], B[source <- k_j])
Z_j    = integral w(g) K_j(g) dg
I_j    = integral w(g) f(g) K_j(g) dg,
```

the normalized change is cross-multiplied before any likelihood ratio is introduced:

```text
Z_1 Z_2 (E_1 f - E_2 f) = I_1 Z_2 - I_2 Z_1.
```

This remains the correct normalization surface because source dependence stays visible and no quotient `K_1 / K_2` obscures its locality.

---

# 4. Explicit source-kernel difference: #4101

PR #4101 closes the algebraic step that was previously listed as the immediate frontier.

The four-integral defect is rewritten so that both the observable-numerator change and the normalizing-mass change depend explicitly on

```text
K_1(g) - K_2(g).
```

Schematically,

```text
I_1 Z_2 - I_2 Z_1
  = Z_2 * integral w f (K_1 - K_2)
      - I_2 * integral w (K_1 - K_2).
```

The theorem introduces exactly the integrability assumptions needed to commute subtraction with the real integral. It assumes no distance decay, no source-kernel ratio estimate, and no identification of the C5 raw law with the full four-dimensional Wilson single-link conditional law.

Therefore `K_1 - K_2` is no longer an open algebraic target. It is an integrated theorem carrier.

---

# 5. Distinct-source scalar factorization: #4103

PR #4103 identifies the exact local structure of the source-kernel difference.

First, the source update of the one-slab kernel is factored through the exact right-boundary source-local Boltzmann factor:

```text
K_1(g) - K_2(g)
  = (L_source(k_1; g) - L_source(k_2; g)) * K_base(g).
```

Here `K_base(g)` is the unmodified one-slab kernel with the left fiber replaced by `g` and the right boundary left at `B`.

Second, if

```text
source != fiber,
```

then replacing the left fiber value does not change the left-boundary coordinate appearing in the source-local factor. The theorem therefore proves

```text
L_source(k; g) = L_source(k)
```

for this distinct-source case.

Consequently,

```text
K_1(g) - K_2(g)
  = (c_1 - c_2) * K_base(g),
```

where `c_1` and `c_2` are independent of the integration variable `g`.

This is stronger structural information than a generic distance-dependent estimate. It says that, for the literal C5 source-kernel difference and `source != fiber`, all fiber dependence is confined to a common base kernel.

It does **not** yet say that the two normalized C5 fiber probability measures are equal. That cancellation is the next theorem.

---

# 6. Why distance decay is no longer the immediate premise

Before #4101/#4103, the natural next step was to search for a summable coefficient such as a distance-sensitive bound on `K_1-K_2`. That remains a valid fallback for any genuinely nonlocal remainder, but it is no longer the first unresolved step in the present C5 route.

The exact theorem now exposes a more rigid possibility:

```text
source != fiber
  -> source change may enter the fiber weight only through a positive scalar.
```

If the individual source-updated C5 weights can be put in the form

```text
W_k(g) = c_k * W_base(g)
```

with `c_k > 0` independent of `g`, then

```text
Z_k = c_k * Z_base
```

and the scalar should cancel from the normalized probability law.

That would yield exact distinct-source invariance on the literal C5 fiber law, which is stronger than a bound of the form

```text
C * exp(-m * d(source,fiber)).
```

But this conclusion must be proved in Lean before it is used. The repository does not treat the cancellation as established merely because the factorization strongly suggests it.

---

# 7. Present mathematical frontier

The immediate theorem-development order is now:

```text
#4103 distinct-source scalar factorization
  -> prove individual positive scalar factorization of the relevant C5 weight
  -> prove partition-function scaling
  -> prove normalized scalar cancellation
  -> prove literal C5 fiber probability equality for source != fiber
  -> derive zero expectation change as a corollary
  -> only then bridge this exact C5 statement back to same-color influence
```

A useful generic normalization lemma may be introduced if needed, for example a theorem saying that multiplying an integrable nonnegative real weight by a positive constant leaves `realIntegralWeightedProbabilityMeasure` unchanged.

The preferred proof route is whichever reuses the existing `doobWeightedMeasure` / real-weight normalization API with the fewest new assumptions. The mathematical statement, not convenience of elaboration, determines the hypotheses.

---

# 8. What must still be checked before claiming remote influence zero

Even if the literal normalized C5 fiber law is proved independent of a distinct right-boundary source value, several bridges remain logically separate.

The repository must still prove exactly how that C5 statement enters the original same-color conditional-dynamics route. In particular, it must not silently identify:

```text
literal C5 reference fiber
```

with

```text
full-4D Wilson singleLinkConditionalMeasure
```

or equate a left/right one-slab source/fiber relation with every same-color remote-link relation without an explicit theorem.

Thus the correct future question is not simply "is the influence zero?" but:

```text
which exact conditional carrier has zero distinct-source dependence,
and which formal bridge transports that zero to the block-coercivity route?
```

Any remaining incidence case where the source is not distinct from the selected fiber must be handled separately and explicitly.

---

# 9. Role of the existing Harnack bound

The volume-independent local Harnack machinery remains valid and useful. The existing comparison scale based on `exp(8 * beta)` and the corresponding variance scale `exp(-16 * beta)` provide robust local positivity and one-link variance control.

What has changed is the role of Harnack in the remote-source problem. A uniform nonzero coefficient summed over all same-color sources loses volume uniformity; that obstruction is already formalized. Therefore Harnack should not be used to replace exact locality by a constant remote bound when the current C5 factorization may instead yield exact cancellation.

If normalized scalar cancellation succeeds, the remote distinct-source part of this particular C5 lane may require no distance decay at all. If some other carrier retains nonzero remote dependence, summable geometry will still be needed there.

---

# 10. Formalized / unproved boundary

Currently formalized on the authoritative theorem carrier include:

- exact finite Wilson and physical-transfer infrastructure;
- the reference one-link RCD / `condExpKernel` route;
- sharp local one-link Harnack and variance comparison;
- raw same-color locality and the link-count obstruction for a constant remote bound;
- covariance / cross-ratio localization;
- the exact `Omega_cont x local x one-slab-kernel` C5 reference-fiber structure;
- quotient-free two-source normalized-change identities retaining both kernels;
- the explicit source-kernel-difference normal form of #4101;
- the #4103 factorization of the source-kernel difference through source-local factors and a common base kernel;
- the #4103 theorem that the source-local factor is fiber-value independent when `source != fiber`;
- the resulting distinct-source scalar-difference-times-base-kernel identity.

Not yet formalized as the next required theorem layer are:

- exact cancellation of a positive source scalar in the normalized literal C5 fiber probability measure;
- equality of the two literal C5 fiber probability measures for distinct source/fiber values;
- a theorem transporting any such exact invariance into the original same-color conditional influence coefficient;
- a volume-independent same-color block-coercivity bound;
- a scale-independent positive twelve-block Poincare coefficient derived from the model;
- a uniform finite-volume physical transfer gap obtained from that coefficient;
- the required thermodynamic/scaling-limit physical carrier with inherited positive gap;
- the full four-dimensional continuum Yang--Mills field/state required by the Clay formulation;
- Clay-level existence and mass gap.

A target-source-distance-sensitive decay theorem is **not currently listed as mandatory for the C5 distinct-source lane**. It becomes necessary only if a later exact bridge leaves a genuinely nonzero remote remainder that is not already eliminated by locality or normalization.

---

# 11. Proof discipline

Repository development follows these rules:

```text
start from the fresh exact canonical theorem-carrier SHA
keep theorem changes additive / tighten-only
separate observed facts from intended estimates
prefer exact cancellation/locality before introducing quantitative decay
never manufacture a decay theorem to close a downstream goal
never generalize a carrier by naming similarity alone
use RED -> diagnose the first genuine Lean failure -> GREEN
never call queued or in-progress CI successful
forbid sorry / admit / new axiom / proof placeholders
merge only against the exact expected work-head
re-observe the authoritative branch after every merge
```

For the ordered next steps, see [`ROADMAP.md`](ROADMAP.md).
