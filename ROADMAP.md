# MGAP4D Roadmap

Status date: 2026-10-04 JST

Authoritative theorem branch:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Latest theorem-bearing baseline before this docs refresh:

~~~text
456825cf29e913d6a5fcd3879e59aec08f16ac9e
~~~

Pinned environment:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

The default branch `main` is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

---

# Executive roadmap

The finite natural-time gap receiver is closed:

~~~text
1/3072 <= physical transfer gap

q0 = 3071/3072 < 1

||R_n^m x|| <= q0^m ||x||.
~~~

The old completed H1-D5 route is a formal no-go and is permanently retired.

The current H1-C3 route is:

~~~text
finite norm-one three-mode excitation
  ->
adjacent finite-union-marginal Krylov comparison
  ->
orbit-wise mismatch
  ->
orbit-wise geometry residual
  +
same-volume normalized coupling residual
  ->
summable / geometric refinement control
  ->
all fixed-natural-time evolved strong limits
  ->
continuum discrete-time q0 dynamics.
~~~

The coupling lane has now been reduced to explicit finite Wilson data through #5112.

The next implementation priority is to assemble the normalized coupling perturbation estimate from #5110/#5111/#5112.

The other remaining H1-C3 input is the orbit-wise **cross-volume geometry/refinement residual**.

After H1-C3, physical-time scaling H2 is a separate problem.

---

# A. Closed foundations

## A1. Finite transfer gap — CLOSED

Already formalized:

- beta = 0 gap = 1;
- positive-beta finite-volume coercivity;
- explicit uniform gap floor;
- one-dimensional finite physical top eigenspace;
- completed pair top-top / non-top decomposition;
- full completed pair non-top q0 power decay.

Canonical receiver:

~~~text
q0 = 3071/3072.
~~~

No new H1-C3 theorem should reprove this layer.

---

## A2. Projective/common finite carriers — CLOSED

The repository has:

- finite projective L2 marginals;
- common finite union marginals for adjacent scales;
- norm-preserving finite-to-projective embeddings;
- coherent fixed Gram--Schmidt modes.

The active route uses these carriers only where needed and does not assume whole operator compatibility.

---

## A3. H1-D4 — CLOSED

Formal theorem:

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Independent endpoint gauge-fixedness is not an open hypothesis.

---

## A4. Completed H1-D5 — CLOSED NO-GO

The old compatibility implies a rank-one normalized transfer and contradicts the explicit positive-coupling SU(2) two-mode sector.

Rule:

~~~text
DO NOT reintroduce:
  completed H1-D5
  vacuum/top alignment
  rank-one forcing
  an equivalent renamed cross-scale operator identity.
~~~

---

## A5. Three-mode finite excitation — CLOSED KINEMATICS

The first three theorem-generated SU(2) Wilson Gram--Schmidt pair modes provide an orthonormal finite synthesis.

Two finite real functionals can be killed simultaneously by a unit vector in `R^3`.

Finite output:

~~~text
||x_n|| = 1

vacuumPairing(x_n) = 0

pairTopPairing(x_n) = 0

x_n in PhysicalPairCarrier

x_n in PairNonTop.
~~~

Thus finite nontriviality is built in before any continuum limit.

---

# B. H1-C3 strong-limit reduction — CLOSED AS IMPLICATION

## B1. #5090--#5097: from operator coherence to finite Cauchy defects

The chain is now:

~~~text
evolved synthesis strong coherence
  ->
three basis Krylov limits
  ->
scalar convergence
  ->
finite self/pair correlations
  ->
candidate-free Cauchy criterion
  ->
one finite union marginal
  ->
finite Cauchy defect.
~~~

Important endpoint:

~~~text
time-zero continuum synthesis is an isometry

||A_infty,0 c|| = ||c||.
~~~

So any unit selected coefficient produces a norm-one continuum initial vector once the Cauchy input is supplied.

Status: REDUCTION CLOSED.

---

## B2. #5098/#5099: all tails -> adjacent summability -> geometric majorant

For every fixed natural time `m` and mode `k`:

~~~text
sum_n d_n^{m,k} < infinity
  ->
Cauchy
  ->
strong limit.
~~~

A sufficient quantitative condition is

~~~text
d_n^{m,k}
  <=
C_{m,k} q_{m,k}^n,

0 <= q_{m,k} < 1.
~~~

Status: FUNCTIONAL-ANALYTIC RECEIVER CLOSED.

---

## B3. #5100--#5103: adjacent transfers on one common marginal

Consecutive scales have common-marginal contractions

~~~text
A_n^L
A_n^R
~~~

with exact Krylov-power representation.

Generic perturbation theorem:

~~~text
||A^m x - B^m y||
  <=
||x-y|| + m ||A-B||.
~~~

Specialized result:

~~~text
d_n^{m,k}
  <=
d_n^{0,k}
  +
m ||A_n^L - A_n^R||.
~~~

The time-zero defect is eventually exactly zero.

Status: CLOSED.

---

## B4. #5104: full-operator geometric route — CLOSED SUFFICIENT ROUTE

If

~~~text
||A_n^L - A_n^R||
  <=
C q^n,

q < 1,
~~~

then all fixed-natural-time strong limits exist and receive q0^m decay.

This route is valid but stronger than necessary.

---

## B5. #5106/#5107: finite Krylov-orbit route — PREFERRED

Generic one-sided telescoping:

~~~text
||A^m x - B^m y||
  <=
||x-y||
  +
sum_{r < m} ||(A-B)(B^r y)||.
~~~

Define

~~~text
e_{n,r,k}
  =
||(A_n^L - A_n^R)
  (A_n^R)^r v_{n,k}^R||.
~~~

For fixed r,k it is enough that

~~~text
sum_n e_{n,r,k} < infinity.
~~~

Or quantitatively:

~~~text
e_{n,r,k}
  <=
C_{r,k} q_{r,k}^n,

q_{r,k} < 1.
~~~

Then all fixed-natural-time evolved strong limits follow.

This is the preferred H1-C3 receiver.

---

# C. Current model-facing split

## C1. #5108: orbit mismatch -> geometry + coupling

The exact preferred split is

~~~text
e_{n,r,k}
  <=
g_{n,r,k}
  +
c_n.
~~~

Here:

~~~text
g_{n,r,k}
  =
orbit-wise cross-volume geometry/refinement residual,

c_n
  =
same-fine-volume normalized physical pair-transfer coupling residual.
~~~

This is the current core decomposition.

The geometry term is vector-wise.

The coupling term is same-volume.

This is much weaker than any global cross-scale transfer compatibility.

---

# D. Coupling lane — actual Wilson data

## D1. #5109 — one-slab kernel beta response CLOSED

For

~~~text
K_beta(A,B)
  =
exp(-beta S_slab(A,B)),
~~~

the repository proves

~~~text
||K_gamma(A,B) - K_beta(A,B)||
  <=
B_H ||gamma-beta||,
~~~

where `B_H` is the explicit finite-volume global Wilson action budget.

No new physical assumption enters.

Status: CLOSED.

---

## D2. #5110 — pair kernel and raw pair transfer response CLOSED

For the ordered-pair kernel:

~~~text
K2_beta = K_beta * K_beta.
~~~

Formal result:

~~~text
||K2_gamma - K2_beta||
  <=
2 B_H ||gamma-beta||.
~~~

The same coefficient is lifted to:

- product-Haar L2 kernel norm;
- raw ambient ordered-pair transfer operator norm.

The square Hilbert--Schmidt kernel-to-operator map is formalized as 1-Lipschitz.

Status: CLOSED.

---

## D3. #5111 — normalization denominator floor CLOSED

Define the explicit global floor

~~~text
m_H(beta)
  =
exp(-beta B_H).
~~~

Formal results:

~~~text
m_H(beta)
  <=
<T_phys 1,1>
  <=
||T_phys(beta)||,
~~~

hence

~~~text
||T_phys(beta)||^(-1)
  <=
m_H(beta)^(-1),
~~~

and

~~~text
(||T_phys(beta)||^2)^(-1)
  <=
(m_H(beta)^2)^(-1).
~~~

This supplies a quantitative denominator certificate for normalized physical pair transfer.

Status: CLOSED.

---

## D4. #5112 — physical transfer norm variation CLOSED

Formal results:

~~~text
||T_phys(gamma) - T_phys(beta)||
  <=
B_H ||gamma-beta||,
~~~

and

~~~text
|||T_phys(gamma)|| - ||T_phys(beta)|||
  <=
B_H ||gamma-beta||.
~~~

This is the numerator needed to estimate variation of the inverse-square normalization scalar.

Status: CLOSED.

---

# E. Immediate next theorem sequence

## E1. Normalization scalar beta variation — NEXT

Set

~~~text
t_beta = ||T_phys(beta)||

a_beta = t_beta^(-2).
~~~

Use:

- positivity of `t_beta`;
- #5111 lower floor `m_H(beta) <= t_beta`;
- #5112 bound on `|t_gamma - t_beta|`.

Target:

~~~text
|a_gamma - a_beta|
  <=
explicit coefficient
    (B_H, m_H(beta), m_H(gamma), ...)
  *
||gamma-beta||.
~~~

Prefer an algebraic theorem that cleanly separates the scalar estimate from the Wilson specialization.

Avoid asking Lean to expand huge continuous-linear-map terms inside inverse-square arithmetic.

---

## E2. Normalized physical pair-transfer beta perturbation — NEXT

Write

~~~text
P_beta = raw physical pair transfer

S_beta = a_beta P_beta.
~~~

Use

~~~text
S_gamma - S_beta
  =
a_gamma (P_gamma - P_beta)
  +
(a_gamma - a_beta) P_beta.
~~~

Available ingredients:

~~~text
||P_gamma - P_beta||
  <=
2 B_H ||gamma-beta||              #5110

a_gamma
  <=
m_H(gamma)^(-2)                   #5111

|a_gamma-a_beta|
  <=
target from E1                    E1

||P_beta||
  <=
existing finite pair contraction
~~~

Target:

~~~text
||S_gamma - S_beta||
  <=
C_norm(H,beta,gamma)
  *
||gamma-beta||.
~~~

This theorem should be stated directly for the normalized physical pair transfer used by #5108.

---

## E3. Specialize to adjacent lattice scales — NEXT

Set

~~~text
H_n = halfExtent(n+1)

beta_left  = beta(n)

beta_right = beta(n+1).
~~~

Then derive

~~~text
c_n
  <=
C_norm(H_n,beta(n),beta(n+1))
  *
||beta(n+1)-beta(n)||.
~~~

This converts the #5108 coupling residual into an explicit scalar sequence.

---

## E4. Coupling summability criterion — NEXT

Prove reusable receivers such as:

~~~text
sum_n
  C_norm(H_n,beta_n,beta_{n+1})
  *
||beta_{n+1}-beta_n||
< infinity

  ->
sum_n c_n < infinity.
~~~

And, where possible:

~~~text
C_norm(...) * ||Delta beta_n||
  <=
C q^n

  ->
geometric coupling summability.
~~~

This closes the coupling half of #5108 under explicit scale assumptions.

---

# F. Geometry lane — main remaining H1-C3 model obstruction

## F1. Orbit-wise geometry residual

The remaining cross-volume object is

~~~text
g_{n,r,k}.
~~~

It compares the coarse/fine common-marginal transfer at one frozen coupling only on

~~~text
(A_n^R)^r v_{n,k}^R.
~~~

Required target:

~~~text
sum_n g_{n,r,k} < infinity
~~~

for every fixed r,k,

or the stronger convenient estimate

~~~text
g_{n,r,k}
  <=
C_{r,k} q_{r,k}^n.
~~~

This should be attacked from the actual refinement/projective Wilson structure.

Do **not** replace it by a full common-transfer operator-norm convergence assumption unless it can be theorem-generated from the model.

---

## F2. Possible refinement strategy

Preferred order:

1. identify exactly which finite Wilson coordinates the fixed orbit vector uses;
2. isolate the additional coordinates introduced from n to n+1;
3. exploit projective/cylinder consistency only on those coordinates;
4. quantify the residual created by projection/compression;
5. prove fixed-r finite-depth locality;
6. derive scale decay or eventual exactness if available.

The fixed orbit depth r is crucial: H1-C3 does not currently require a bound uniform in all Krylov depths.

---

# G. Close actual H1-C3 once E + F are available

Given:

~~~text
sum_n g_{n,r,k} < infinity

sum_n c_n < infinity,
~~~

#5108 gives:

~~~text
sum_n e_{n,r,k} < infinity.
~~~

Then #5106 gives, for every fixed natural time m,k:

~~~text
sum_n d_n^{m,k} < infinity.
~~~

Then #5098/#5096 give Cauchy and strong limits.

The continuum synthesis remains norm-one at time zero by #5097.

The fixed-natural-time q0 receiver then yields

~~~text
||z_infty,m|| <= q0^m
~~~

for the theorem-generated limiting excitation.

At this stage H1-C3 existence of all fixed natural-time evolved vectors is model-facing closed.

A further theorem should then package compatibility in m into a single discrete-time continuum transfer where justified.

---

# H. Discrete-time operator identification

After fixed-m limits exist, verify:

1. same chosen subsequence works for all required fixed m, or use a diagonal construction;
2. limits respect the finite semigroup recursion;
3. define a continuum operator T on the generated excitation subspace;
4. prove
   ~~~text
   z_infty,m = T^m z_infty,0;
   ~~~
5. prove contraction / q0 estimate on the generated non-top sector.

Do not assert a continuum operator before this compatibility step is formalized.

---

# I. H2 — physical-time scaling

H2 is not solved by fixed q0.

For lattice spacing `a_n -> 0`:

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed positive physical time.

A nontrivial continuum semigroup requires a spacing-sensitive rate, for example

~~~text
q_n
  =
exp(-m_n a_n + o(a_n)).
~~~

Possible formal interfaces:

- transfer logarithm;
- rescaled Dirichlet form;
- Poincare lower bound;
- generator lower bound;
- direct semigroup convergence.

H2 begins only after H1-C3 supplies actual continuum discrete-time dynamics.

---

# J. H3 — OS Hamiltonian

Required outputs:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry / self-adjointness;
- closed nonnegative Hamiltonian;
- identified vacuum-orthogonal excitation sector.

Generic operator-theoretic infrastructure exists.

The missing work is the actual model bridge.

---

# K. H4 — spectral / Wightman mass gap

Final intended route:

~~~text
finite Wilson coercivity
  ->
finite norm-one non-top excitation
  ->
projective evolved strong limits
  ->
continuum discrete-time transfer
  ->
physical-time scaling
  ->
OS Hamiltonian
  ->
vacuum-orthogonal spectral lower bound
  ->
positive physical mass
  ->
Wightman / energy-momentum mass gap.
~~~

No current theorem claims this final chain is complete.

---

# L. Lean implementation rules

## L1. Exact environment

Always use the pinned environment:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

Current mathlib master is only a hint.

---

## L2. Full-file CI repair

When CI fails:

- inspect the entire changed file;
- inspect all diagnostics, not only the first red line;
- distinguish parser, elaboration, coercion, typeclass, and mathematical failures;
- re-read neighboring theorem signatures;
- prefer smaller proof terms over heartbeat increases.

---

## L3. Typeclass synthesis lessons from #5105/#5106/#5111/#5112

Repeated failure mode:

~~~text
failed to synthesize SeminormedAddGroup / Nontrivial
for a huge ContinuousLinearMap type
deterministic timeout.
~~~

Preferred repairs:

- avoid `simpa [huge definitions]`;
- use `change` to expose the real scalar/order target;
- fully apply `ContinuousLinearMap.opNorm_le_bound`;
- reuse an existing positivity theorem instead of `norm_nonneg _` when `_` forces reconstruction of a huge operator type;
- use `simpa only` for final scalar rewrites;
- keep operator-valued and scalar-valued proof phases separate.

Do not solve this class of problem by simply increasing heartbeats.

---

## L4. Section-variable pruning

Lean only retains section variables that appear in the generated declaration signature.

Therefore:

- do not assume every section variable is an explicit theorem argument;
- use named arguments such as
  ~~~text
  (halfExtent := halfExtent)
  ~~~
  where needed;
- inspect the actual theorem signature after pruning.

---

## L5. CI merge rules

For theorem-bearing PRs require:

~~~text
exact head unchanged
+
PR Lean Fast Check success
+
matching exact-head receipt success.
~~~

For docs-only PRs:

- strict Lean rerun is unnecessary if no Lean file changed;
- docs-only commits do not become the theorem-bearing authority.

---

# M. Recent milestone ledger

| PR | Status | Contribution |
| --- | --- | --- |
| #5090 | merged | reduce evolved limits to three-mode synthesis coherence |
| #5091 | merged | reduce to three Krylov basis limits |
| #5092 | merged | scalar convergence criterion |
| #5093 | merged | 2m-step self-correlation identity |
| #5094 | merged | Cauchy construction without prechosen continuum vector |
| #5095 | merged | pair correlations moved to finite union marginals |
| #5096 | merged | common-marginal Cauchy defect |
| #5097 | merged | time-zero continuum synthesis isometry |
| #5098 | merged | summable adjacent defects |
| #5099 | merged | geometric adjacent defect route |
| #5100 | merged | contraction-power perturbation |
| #5101 | merged | time-zero adjacent defect eventually zero |
| #5102 | merged | adjacent common-marginal transfers |
| #5103 | merged | adjacent defect <= time-zero + m operator mismatch |
| #5104 | merged | geometric full operator mismatch receiver |
| #5105 | merged | operator mismatch split into geometry + coupling |
| #5106 | merged | finite Krylov-orbit telescoping route |
| #5107 | merged | geometric orbit mismatch receiver |
| #5108 | merged | orbit-wise geometry + coupling split |
| #5109 | merged | exact one-slab kernel beta-Lipschitz |
| #5110 | merged | pair kernel/L2/raw pair transfer beta-Lipschitz |
| #5111 | merged | explicit normalization floor and inverse-square bound |
| #5112 | merged | physical transfer/operator-norm beta response |

---

# N. Immediate implementation order

## N1 — inverse-square normalization variation

Prove a scalar lemma and specialize to the physical transfer norm.

## N2 — normalized pair-transfer beta perturbation

Combine #5110/#5111/#5112.

## N3 — adjacent-scale coupling residual

Specialize N2 to `beta(n)` and `beta(n+1)`.

## N4 — coupling summability/geometric criterion

Feed N3 into #5108.

## N5 — orbit-wise geometry refinement estimate

Attack `g_{n,r,k}` from actual finite Wilson/projective refinement data.

## N6 — actual H1-C3 strong limits

Use #5108 -> #5106 -> #5098/#5096.

## N7 — continuum discrete-time transfer identification

Package fixed-m limits into one operator where the semigroup identities permit it.

## N8 — H2 physical-time scaling

Introduce spacing-sensitive rates.

## N9 — OS Hamiltonian and spectral mass gap

Only after H1/H2 model data exist.

---

# O. Restart instructions

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Expected theorem-bearing baseline at this docs checkpoint:

~~~text
456825cf29e913d6a5fcd3879e59aec08f16ac9e
~~~

but fresh GitHub state always takes precedence.

Read first:

1. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor.lean` — #5111
2. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz.lean` — #5112
3. `PeriodicHypercubicEvenSpecialUnitaryOneSlabPairBetaLipschitz.lean` — #5110
4. `PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz.lean` — #5109
5. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatchSplit.lean` — #5108
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitGeometric.lean` — #5107
7. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentOrbitMismatch.lean` — #5106
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransfer.lean` — #5102
9. `ContinuousLinearMapContractionPowerPerturbation.lean` — #5100

Current handoff:

~~~text
CLOSED:
  finite q0 receiver
  H1-D4
  completed H1-D5 no-go
  finite norm-one three-mode non-top excitation
  time-zero continuum nontriviality
  adjacent-defect Cauchy receiver
  common-marginal transfer representation
  orbit-wise telescoping receiver
  orbit geometry/coupling split
  one-slab beta Lipschitz
  raw pair-transfer beta Lipschitz
  explicit normalization floor
  physical transfer-norm beta Lipschitz

NEXT:
  normalized pair-transfer beta perturbation
  ->
  explicit adjacent coupling residual
  ->
  coupling summability

PARALLEL / NEXT:
  orbit-wise cross-volume geometry estimate

THEN:
  actual H1-C3 fixed-time strong limits
  ->
  continuum discrete-time transfer

THEN:
  H2 spacing-scaled physical time

LATER:
  OS Hamiltonian
  ->
  spectral / Wightman mass gap.
~~~
