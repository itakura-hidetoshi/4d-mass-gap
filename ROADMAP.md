# MGAP4D ROADMAP

## Authority checkpoint — 2026-09-29 JST

Repository:

`itakura-hidetoshi/4d-mass-gap`

Authoritative theorem-carrier branch:

`formal/real-hilbert-uniform-coercive-strong-limit`

Current theorem-bearing HEAD:

`696fd06775636f31f0364e331103a009cc729fde`

This is the merge commit of PR #4899.

Pinned environment:

- Lean `v4.30.0-rc2`
- mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / memory.

The GitHub default branch `main` is not theorem authority.

---

## 0. Claim boundary

The finite-volume Wilson / OS / physical-transfer construction is highly
developed, the beta-zero endpoint has an exact physical transfer gap, and the
positive-beta response / Schur machinery is largely formalized.

The continuum four-dimensional Yang--Mills existence and mass-gap problem is
not yet formally closed.

The active bottleneck is the finite-volume positive-beta physical gap:
the noncommutative same-color one-link sweep must be compared quantitatively
with the genuine color-block projection without introducing a
volume-dependent loss.

PRs #4892--#4899 now provide the exact renewal geometry, cyclic second-visit
carrier, bounded representatives, terminal profile, response energy receiver,
Schur feedback receiver, and exact off-diagonal cyclic source set.  The
remaining task is semantic / quantitative rather than combinatorial.

---

## 1. Fixed notation for the current frontier

For one spatial color `c`:

```text
B_c  = genuine spatial-color conditional expectation
S_c  = one complete canonical same-color one-link sweep
L_c(f) = exact sweep path loss
D_c(f) = ||S_c f - B_c f||^2
```

Six-color normalized quantities:

```text
L(f)
  = (1/6) * sum_c L_c(f)

Dmean(f)
  = (1/6) * sum_c D_c(f)

Lterm(f)
  = (1/6) * sum_c L_c(S_c f)

Dnext(f)
  = (1/6) * sum_c D_c(S_c f)
```

The exact obstruction identity already closed before the renewal work is

```text
E_6sp(f) = L(f) + Dmean(f).
```

The full-sweep retained-norm identity is

```text
FullSweepMean(f)
  = MeanProjectedNormSq(f) + Dmean(f).
```

The transfer-gap defect-margin receiver is already available:
if on the physical sector

```text
Dmean(f) <= delta * ||f||^2
0 <= delta < 1/6,
```

then

```text
(3/8) * (1/6 - delta)
  <= physical transfer gap.
```

Thus the current finite-volume task is to produce a certified
`delta(beta) < 1/6` on a volume-independent positive-beta interval.

---

## 2. Exact beta-zero anchor

The beta-zero endpoint is closed independently of the perturbative receiver.

### 2.1 Pair-Haar / same-color sweep

PRs #4887--#4888 prove:

- pair-Haar one-link retained-space invariance;
- pairwise commutation at beta zero;
- complete same-color pair-Haar sweep = pair-Haar color block.

PR #4889 transports this to the genuine beta-zero carrier:

```text
S_c,0 = B_c,0
D_c,0(f) = 0
Dmean_0(f) = 0.
```

The exact physical transfer gap at beta zero remains

```text
gap_0 = 1.
```

The perturbative receiver can also be evaluated at `delta(0)=0`, but that
weaker bound is not the beta-zero theorem and must not be confused with the
exact result.

---

## 3. Positive-beta common fixed geometry

PR #4890 identifies the common fixed space for every `beta >= 0`:

```text
(forall e in color c, Q_e x = x)
  <-> B_c x = x
```

and

```text
S_c x = x
  <-> B_c x = x.
```

This does **not** assert positive-beta commutativity and does not assert
`S_c = B_c`.

PR #4891 identifies the defect vector with the terminal color residual:

```text
S_c f - B_c f
  = S_c f - B_c(S_c f).
```

Hence

```text
D_c(f) = 0
  <-> B_c(S_c f) = S_c f
  <-> S_c(S_c f) = S_c f.
```

The defect is therefore the exact obstruction to one-pass idempotence.

---

## 4. Exact defect renewal — PR #4892

For each color:

```text
D_c(f) = L_c(S_c f) + D_c(S_c f).
```

Consequences already formalized:

```text
D_c(S_c f) <= D_c(f).
```

If a strict next-defect estimate is supplied,

```text
D_c(S_c f) <= rho * D_c(f),
```

then

```text
(1-rho) * D_c(f) <= L_c(S_c f).
```

If in addition

```text
L_c(S_c f) <= eta * L_c(f),
```

then

```text
(1-rho) * D_c(f) <= eta * L_c(f).
```

No division by `1-rho` is performed at this stage.

---

## 5. Vector renewal — PR #4893

PR #4893 exposes the exact vector carrier behind the energy renewal:

```text
defectVector_c(f)
  = residualVectorSum_c(S_c f)
    + defectVector_c(S_c f).
```

Equivalently:

```text
residualVectorSum_c(S_c f)
  = defectVector_c(f)
    - defectVector_c(S_c f).
```

For a canonical split

```text
canonicalList = pre ++ e :: suffix,
```

the second-sweep residual-vector sum is exposed as

```text
prefix residual sum
+ e-stage residual
+ suffix residual sum
+ next defect vector.
```

This is the exact vector-level entry point for the response machinery.

---

## 6. Cyclic second visit — PR #4894

For any ordered family of continuous linear maps, PR #4894 proves

```text
sweep pre (sweep (pre ++ e :: suffix) x)
  =
sweep (suffix ++ pre) (P_e (sweep pre x)).
```

Thus the second visit to target `e` is separated from the first visit by the
exact cyclic order

```text
suffix ++ pre.
```

The corresponding second-visit residual identity is also formalized.

After specialization to the genuine fixed-color one-link conditional
expectations:

```text
secondSweepStageResidual_e
  =
targetResidual_e
  after cyclic propagation through suffix ++ pre.
```

No reordering or commutativity is used.

---

## 7. Bounded cyclic representatives — PR #4895

Every finite same-color one-link sweep preserves the bounded concrete core.

PR #4895 reapplies the canonical-prefix representative theorem to `S_c f`
and combines it with the PR #4894 cyclic identity.

For each target `e` there is a bounded strongly measurable concrete
representative satisfying exactly

```text
boundedRepresentative_e
  =
sweep (suffix_e ++ pre_e)
  (Q_e (sweep pre_e f)).
```

The coefficient-one canonical fiber residual bound is retained against the
actual terminal second-sweep local profile.

The representative data are also chosen simultaneously for the full finite
spatial-link family.

This closes the carrier compatibility needed by the physical
direct/backward/law-response theorems.

---

## 8. Terminal profile / averaged renewal — PR #4896

Define the terminal fixed-color profile by evaluating the ordinary canonical
sweep-stage profile on `S_c f`.

For each color:

```text
sum_{e in c} terminalProfile_c(e)^2
  = L_c(S_c f).
```

After reindexing all color fibers back to genuine spatial links:

```text
(1/6) * sum_e terminalProfile(e)^2
  = Lterm(f).
```

PR #4896 also defines `Dnext(f)` and averages PR #4892:

```text
Dmean(f) = Lterm(f) + Dnext(f).
```

The terminal profile is now the canonical link-indexed energy carrier for the
renewal step.

---

## 9. Terminal response energy — PR #4897

A generic coefficient-one profile bridge is now public.

If the selected bounded representatives satisfy

```text
||r_e|| <= profile(e)
```

for every target, then

```text
sum_e CanonicalFiberVariance(e)
  <= ofReal(sum_e profile(e)^2).
```

The existing full-response theorem therefore gives

```text
fullResponseEnergy
  <= rhoResp(s,beta)
     * ofReal(sum_e profile(e)^2).
```

Inserting the PR #4895 cyclic second-sweep representative family and the
terminal profile yields

```text
terminalResponseEnergy
  <= rhoResp(s,beta)
     * ofReal(6 * Lterm(f)).
```

This keeps the same volume-independent response coefficient already proved in
the earlier response spine.

The strict response interval remains characterized by

```text
rhoResp(s,beta) < 1.
```

---

## 10. Terminal-profile Schur feedback — PR #4898

The existing transpose Schur receiver is specialized to the terminal profile.

Premise:

```text
terminal(source)
  <= originalLocal(source)
     + sum_target K(target,source) * terminal(target).
```

Conclusion:

```text
(1 - q_phys(s,beta))^2 * Lterm(f)
  <= L(f).
```

The same theorem unit packages the averaged renewal receiver.

If

```text
Dnext(f) <= rho * Dmean(f),
```

then

```text
(1-rho) * Dmean(f)
  <= Lterm(f).
```

Combining the two supplied premises:

```text
(1-q_phys)^2 * ((1-rho) * Dmean(f))
  <= L(f).
```

This is deliberately coefficient-preserving.  It performs no division before
strict positivity is formally available.

Important limitation:

The current one-sided receiver has coefficient one in front of the original
local profile.  It is a structural receiver, not by itself a proof of the
small margin `delta(beta) < 1/6`.  The next semantic estimate must retain the
beta-small structure needed near the exact beta-zero endpoint.

---

## 11. Exact cyclic source set — PR #4899

For

```text
canonicalList = pre ++ e :: suffix
```

with the preserved freshness witness:

```text
d ∈ suffix ++ pre
  <-> d != e
```

inside the fixed-color fiber.

Finset form:

```text
(suffix ++ pre).toFinset
  = Finset.univ.erase e.
```

Therefore the between-visits list contains exactly every other link of the
same color and never contains the target.

After forgetting the fixed-color subtype, every cyclic source satisfies the
required off-diagonal hypothesis

```text
source != target.
```

This closes the source-set geometry needed to invoke the direct / backward /
transposed response API without reordering or cardinality estimates.

---

## 12. Closed machinery to reuse

### 12.1 Canonical sweep / stage residual machinery

Closed:

- canonical prefix + suffix witness;
- exact vector sweep telescoping;
- exact stage residual exposure;
- local profile = exact stage residual norm;
- stage residual squared sum = sweep path loss;
- bounded-core preservation under every finite same-color sweep.

Do not rebuild these.

### 12.2 Response / Schur machinery

Closed:

- canonical target-law response L2;
- first-cross exact variance split;
- Harnack old-to-updated variance transport;
- stationarity return;
- genuine target residual / canonical fiber variance;
- fixed-background response Fubini;
- configuration-independent pin-free row + column control;
- transpose Schur action;
- strict positive response cutoff;
- full response-sum energy bounds.

### 12.3 Exact physical full/direct/response decomposition

Closed:

```text
fullDifferenceL2
  = directDifferenceL2 + responseL2
```

for every off-diagonal target/source pair, together with the semantic
identification with actual source-updated centered means.

### 12.4 Direct / backward machinery

Closed:

- exact DirectDifferenceL2 energy realization;
- coefficient-one direct L2 -> ordered direct-average comparison;
- ordered direct energy -> backward reversible carrier;
- exact backward direct fiber Pythagorean split;
- backward centered variance -> genuine source residual;
- current-value reference reanchoring;
- backward law-response = negative transposed canonical response;
- backward law-response heat-bath energy = transposed response L2 norm squared;
- transposed law-response control by the original source residual.

The transposed coefficient orientation is fixed:

```text
K_pin(source,target)
```

for the PR #4878 backward law-response theorem.

Do not silently replace it by a symmetric coefficient.

---

## 13. Immediate frontier after PR #4899

The list geometry, target revisit order, bounded representative carrier, and
terminal energy normalization are closed.

The next task is to prove the actual semantic source-update estimate along the
cyclic list `suffix ++ pre`.

### 13.1 Target theorem shape

For each target/source orientation, use the exact cyclic source set and the
existing source-update decomposition to derive a one-sided terminal-profile
recurrence.

The coarse receiver-ready shape is

```text
terminalProfile(source)
  <= originalProfile(source)
     + sum_target K(target,source) * terminalProfile(target).
```

However, for the final defect margin the proof should preserve a sharper
beta-small coefficient whenever the exact decomposition provides one:

```text
terminalProfile(source)
  <= a(beta) * originalProfile(source)
     + sum_target K_beta(target,source) * terminalProfile(target),
```

with the goal that the induced terminal path-loss coefficient tends to zero at
beta zero.

Do **not** prematurely normalize `a(beta)` to one if that destroys the
beta-zero smallness needed for `delta(beta) < 1/6`.

### 13.2 Required ingredients for each cyclic source update

For every source in `suffix ++ pre`, PR #4899 provides `source != target`.

Use:

1. exact physical source-update semantic identity;
2. `full = direct + response`;
3. direct L2 exact energy realization;
4. backward reversible-carrier transport;
5. centered-variance / mean-square split;
6. coefficient-one source residual control for the centered variance;
7. exact local + law-response split for the backward mean;
8. current-value reanchoring;
9. negative transposed response identity;
10. transposed response energy bound with the correct source/target
    orientation.

The assembly must remain ordered and volume-uniform.

### 13.3 Forbidden shortcuts

Do not use:

- finite-cardinality Cauchy over all cyclic sources;
- a factor proportional to the number of same-color links;
- an arbitrary factor two from squaring a direct + response sum;
- response symmetry;
- positive-beta commutativity;
- carrier identification without an exact map;
- pointwise evaluation of an arbitrary L2 quotient representative.

---

## 14. Terminal path-loss feedback target

Once the semantic one-sided terminal recurrence is proved, feed it to the
PR #4898 Schur receiver.

The current coefficient-one receiver gives

```text
(1-q_phys)^2 * Lterm <= L.
```

If the semantic theorem carries an additional small coefficient `a(beta)`,
add the corresponding sharpened receiver rather than discarding that
coefficient.

Desired quantitative form:

```text
Lterm(f) <= eta(beta) * L(f)
```

with `eta(beta)` explicit, volume-independent, and small enough near
`beta=0` for the later defect-margin estimate.

---

## 15. Strict next-defect contraction

A separate quantitative ingredient remains open:

```text
Dnext(f) <= rhoDefect(beta) * Dmean(f)
rhoDefect(beta) < 1.
```

Equivalent usable forms are acceptable, for example a certified lower bound

```text
kappa(beta) * Dmean(f) <= Lterm(f)
```

with `kappa(beta) > 0`.

The exact renewal

```text
Dmean = Lterm + Dnext
```

must be used rather than an abstract convergence argument for cyclic
projections.

The proof should exploit the already-exposed cyclic source-update response
structure and beta-zero vanishing, not introduce a volume-dependent
finite-dimensional spectral constant.

---

## 16. Defect margin closure

After obtaining

```text
Lterm <= eta(beta) * L
```

and

```text
Dnext <= rhoDefect(beta) * Dmean,
```

use the coefficient-preserving renewal receiver:

```text
(1-rhoDefect(beta)) * Dmean
  <= eta(beta) * L.
```

Only after proving

```text
0 < 1-rhoDefect(beta)
```

should division be performed.

Then derive an explicit

```text
Dmean(f) <= delta(beta) * ||f||^2.
```

The target is

```text
delta(beta) < 1/6.
```

No numerical positive-beta constant should be frozen before all coefficients
and positivity hypotheses are formally closed.

---

## 17. Positive-beta finite-volume physical transfer gap

Once

```text
0 <= delta(beta) < 1/6
```

is established on the physical sector, invoke the existing defect-margin
receiver:

```text
(3/8) * (1/6 - delta(beta))
  <= physical transfer gap.
```

Keep this perturbative positive-beta receiver distinct from the exact
beta-zero theorem `gap_0 = 1`.

The resulting lower bound must be volume-independent.

---

## 18. Full-L2 / bounded-core closure

The bounded concrete core is already dense and stable under the relevant
one-link sweeps.

Once the finite-volume physical coercive estimate is closed:

1. extend from the bounded concrete core to the full genuine joint L2 carrier
   using the existing closure / continuity theorems;
2. pass through the already-built physical-sector / Rayleigh / transfer-gap
   receivers;
3. record the explicit volume-independent positive-beta interval and gap
   coefficient.

Do not reopen the older pointwise RMS route whose outer-energy / pointwise
mismatch was already identified.

---

## 19. Thermodynamic / infinite-volume stage

Only after the volume-uniform finite-volume physical gap is formalized should
this become the active frontier.

Required work includes:

- compatible finite-volume embeddings / restrictions;
- uniform control of the vacuum sector;
- thermodynamic limiting state;
- transfer / semigroup compatibility;
- persistence of the positive spectral gap in the appropriate limiting
  carrier.

No continuum claim should be inferred merely from a finite-volume gap theorem.

---

## 20. Continuum OS / Wightman stage

Subsequent tasks include:

- continuum Euclidean field limit;
- Osterwalder--Schrader axioms at the continuum level;
- reflection-positive reconstruction;
- strongly continuous physical time translations;
- self-adjoint Hamiltonian;
- vacuum uniqueness / sector identification;
- relation between the limiting transfer gap and Hamiltonian spectral gap;
- Wightman reconstruction and the final continuum mass-gap statement.

These remain downstream OPEN goals.

---

## 21. Recent theorem-bearing PR sequence

| PR | Status | Merge commit | Role |
| --- | --- | --- | --- |
| #4887 | merged | `48d543ea1b14ce9098b951029de25f57b325fa0e` | beta-zero pair-Haar commutation |
| #4888 | merged | `029370c4d2386597f0f048814ff1d2fa7b6887e0` | beta-zero same-color sweep = block |
| #4889 | merged | `d6d0fe928b1a076ffe249b37a245b96ba631109a` | beta-zero sweep-block defect = 0 |
| #4890 | merged | `5cd36ea2666600cc2baa49e038f9800ac72aafbf` | positive-beta common fixed geometry |
| #4891 | merged | `6931db42b0fb722f39c84e537467e1ecffced78d` | terminal defect geometry |
| #4892 | merged | `2727e50414cd2f6373a2fbde89ab3c71a47e3672` | exact defect renewal |
| #4893 | merged | `847e21e62321f4061f1945455bb17977f687409b` | vector renewal |
| #4894 | merged | `551fe25176f2d723dcc54c80f2fda723fece57fd` | cyclic second visit |
| #4895 | merged | `1bacd3da86db26027ba5ade88a837b4ff7331bd6` | bounded cyclic representatives |
| #4896 | merged | `866770a7215a9a1564d2416e41f177857f4e98ae` | terminal profile / averaged renewal |
| #4897 | merged | `6091310e11647fd19b523abfc93f97578fa0a81d` | terminal response energy |
| #4898 | merged | `f67a2afdc7083aef9218b6dc2ec8c31d72ec1dac` | terminal-profile Schur feedback receiver |
| #4899 | merged | `696fd06775636f31f0364e331103a009cc729fde` | exact cyclic source set |

---

## 22. Lean 4 / mathlib engineering rules

1. Fresh re-observe the theorem-carrier before any new theorem branch.
2. Classify only the current exact PR head SHA.
3. The theorem-bearing GREEN criterion is:
   - completed `PR Lean Fast Check` = success;
   - exact-head `chatgpt-ci-receipt/PR Lean Fast Check` = success;
   - PR mergeable.
4. Do not rerun Strict Lean merely because an already-passing theorem PR exists.
5. Docs-only PRs do not require Strict Lean.
6. On RED, inspect the full changed Lean file, CompileSmoke, imports, dependent
   signatures, typeclass instances, and pinned mathlib API.
7. Pinned mathlib is theorem authority.
8. Prefer local aliases + `calc` over giant dependent `rw` / `unfold`.
9. Local instances do not cross import boundaries; reintroduce named local
   instances where required.
10. Keep `norm_num` local to the intended numeric coefficient; do not
    simplify an entire hypothesis when that could erase its structure.
11. Preserve source/target orientation exactly.
12. Never infer response symmetry.
13. Avoid finite-cardinality Cauchy and arbitrary factor-two losses.
14. Do not pointwise evaluate arbitrary L2 quotient representatives.
15. Do not identify measure-indexed carriers without explicit transport.
16. Do not assume positive-beta one-link projections commute.

---

## 23. Restart instruction

At the start of the next theorem thread:

1. fresh re-observe
   `formal/real-hilbert-uniform-coercive-strong-limit`;
2. expected theorem-bearing baseline is
   `696fd06775636f31f0364e331103a009cc729fde`
   unless a later theorem merge exists;
3. retain #4887--#4889 as the exact beta-zero sweep/block anchor;
4. retain #4890--#4892 as common-fixed geometry + terminal geometry + renewal;
5. retain #4893--#4895 as vector renewal + cyclic second visit + bounded cyclic
   representatives;
6. retain #4896--#4898 as terminal profile + response energy + Schur feedback
   receiver;
7. retain #4899 as the exact cyclic off-diagonal source-set theorem;
8. do not rebuild canonical prefix, telescoping, stage-residual, RMS,
   fixed-background response, Schur, or backward-response infrastructure;
9. begin from the actual ordered cyclic source-update semantics on
   `suffix ++ pre`;
10. use #4899 to discharge every `source != target` premise;
11. preserve direct + response decomposition and transposed coefficient
    orientation;
12. derive a volume-uniform terminal-profile one-sided estimate while
    retaining beta-small coefficients;
13. separately close strict next-defect contraction;
14. combine them through #4898 and the exact averaged renewal;
15. derive `Dmean <= delta(beta) * ||f||^2`;
16. certify `delta(beta) < 1/6`;
17. invoke the existing transfer-gap receiver;
18. only then advance the thermodynamic / continuum construction.

The immediate mathematical frontier is:

```text
cyclic between-visits source-update semantics
  -> beta-small terminal-profile recurrence
  -> terminal Schur feedback
  + strict renewal contraction
  -> delta(beta) < 1/6
  -> positive-beta finite-volume physical transfer gap.
```
