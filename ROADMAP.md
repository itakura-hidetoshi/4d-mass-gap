# MGAP4D Roadmap

Status date: 2026-10-04 JST

Authoritative theorem branch:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Latest theorem-bearing baseline before this docs refresh:

~~~text
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Latest theorem-bearing branch tip contains both adjacent theorem lines:

~~~text
#5078
Add three-mode two-functional unit-kernel lemma

#5077
Realize all SU(2) Gram-Schmidt Wilson modes as physical pairs

final branch tip after #5077 merge:
426ad4fe783d030a61687fbb123aca00b90a3d1d
~~~

Exact validation:

~~~text
#5077 head:
  aaa6d50c2da21461a76a6a0e6e2f9ee72b518998
#5077 PR Lean Fast Check:
  37157037971
  completed / success
#5077 exact-head receipt:
  success

#5078 head:
  61acb9b380ee3822e5574c1e9fd56e61cba5d64f
#5078 PR Lean Fast Check:
  37156892868
  completed / success
#5078 exact-head receipt:
  success
~~~

Pinned environment:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

The default branch main is not theorem authority.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. exact-head CI receipts;
5. history / conversation memory.

Docs-only commits are not theorem-bearing baselines.

---

## 0. Executive state

The finite-volume spectral/coercive side is substantially closed.

The exact quantitative endpoint is:

~~~text
1/2304 <= kappa_12(s,beta)

1/3072 <= physical top-eigenspace transfer gap

q0 = 3071/3072

||R_n^m x|| <= q0^m ||x||
~~~

with the q0 estimate extended to the full completed physical pair non-top sector.

The old completed H1-D5 compatibility is formally refuted at positive SU(2) coupling.

The current task is no longer to prove a vacuum-identification seam.

The active route is now:

~~~text
three theorem-generated coherent orthonormal SU(2) pair modes (#5077)
  +
abstract Fin-3 two-functional unit-kernel selector (#5078)
  ->
instantiate two exact finite scalar constraints
  ->
one normalized nonzero physical non-top pair at every scale
  ->
existing q0^m estimate
  ->
projective strong limit
  ->
evolved projective dynamics
  ->
physical-time scaling
  ->
OS Hamiltonian / mass gap.
~~~

---

## 1. Closed finite-volume quantitative route

Already formalized:

- beta = 0 gap = 1;
- positive-beta finite-volume coercivity;
- explicit high-temperature uniform gap floor;
- one-dimensional physical top eigenspace;
- top-orthogonal natural-power decay;
- completed pair top-top / non-top decomposition;
- pair-top one-dimensionality;
- full completed pair non-top q0 power decay.

The explicit common factor remains

~~~text
q0 = 3071/3072 < 1.
~~~

This part should be treated as a reusable receiver, not repeatedly reproved.

---

## 2. Projective finite-scale carrier — closed kinematics

PRs #4993--#4998 establish the projective L2 carrier used for thermodynamic/common-scale comparison.

Important distinction:

### Independent-product lane

Useful for simultaneous finite-scale comparison.

But fresh-coordinate centered sequences can vanish in the limit.

### Projective lane

Keeps compatible cylinder information across scales and supports nonzero strong limits.

All current continuum-side work should stay on this projective lane.

---

## 3. Explicit finite Wilson pair route — closed

PRs #4999--#5016 provide:

- explicit SU(N) primary-plaquette Wilson modes;
- finite physical one-slice representatives;
- explicit ordered endpoint-pair representatives;
- one-dimensional top eigenspace;
- one-dimensional completed pair TopTop block;
- q0 control on the completed non-top receiver.

These modules are the finite kinematic base used by the later no-go and replacement routes.

---

## 4. Canonical-sign OS vacuum and H1-D4 — closed

### #5017/#5018

The canonical-sign finite OS vacuum is identified with the concrete Wilson boundary vacuum.

Its pair representative is fixed by arbitrary independent endpoint gauge transformations.

### #5022--#5029

The repository proves

~~~text
IndependentEndpointGaugeFixedPairSector
  =
PhysicalPairCarrier.
~~~

Thus the canonical-sign OS vacuum pair is physical without any H1-D5 transfer compatibility.

Status: CLOSED.

Do not list H1-D4 as an open seam.

---

## 5. Old completed H1-D5 — formally refuted

PRs #5031--#5061 show that the old completed compatibility is not a harmless technical assumption.

The reduction is:

~~~text
completed H1-D5
  ->
literal finite Wilson identity
  ->
positive-half transfer power identity
  ->
top-orthogonal restriction = 0
  ->
rank-one normalized one-slab transfer
  ->
two-mode Gram degeneracy
  ->
feature-analysis kernel nontrivial.
~~~

The positive-coupling SU(2) strictness chain proves the opposite finite statement on the explicit two-mode sector.

Therefore:

~~~text
beta(n) > 0
  ->
not H1-D5 completed compatibility at scale n.
~~~

Status: CLOSED NO-GO.

Rule:

~~~text
Do not resurrect completed H1-D5,
vacuum/top alignment,
or an equivalent rank-one-forcing statement.
~~~

---

## 6. Post-no-go centered scalar replacement — #5063/#5064

### #5063

The actual vacuum-normalized centered pair receives an exact top-pair scalar expansion.

The associated excitation-level scalar compatibility is strictly weaker than H1-D5.

### #5064

The old SU(2) global vacuum/top alignment route is explicitly excluded.

This is an important design constraint for every later theorem.

---

## 7. Canonical projected non-top finite excitation — #5065--#5067

### #5065

For the actual centered finite pair, define:

~~~text
TopTop projection
NonTop projection.
~~~

The projected vector is automatically:

~~~text
in PhysicalPairCarrier,
orthogonal to TopTop,
therefore controlled by q0^m.
~~~

No transfer compatibility is assumed.

### #5066

Nonzero projected excitation is reduced to a nonzero finite OS-vacuum / pair-top overlap.

### #5067

That overlap is proved strictly positive.

Hence at every finite scale:

~~~text
exists k : Fin 2,
projected centered mode k != 0,
and
||S_pair^m x|| <= q0^m ||x||.
~~~

Status: CLOSED.

---

## 8. Common projective carrier for projected modes — #5068/#5069

### #5068

Embed the projected non-top finite modes into one common projective continuum L2 carrier.

The embedding is norm preserving.

### #5069

Among the two selected labels, choose one fixed label on an infinite increasing scale subsequence such that the projected mode stays nonzero.

This establishes a robust finite-to-projective kinematic lane.

Status: CLOSED.

---

## 9. Strong-convergence factorization — #5070--#5074

### #5070

The projected common image is exactly

~~~text
centered common image
  -
<top common image, centered common image>
  * top common image.
~~~

So the scalar coefficient is not an independent object.

### #5071

The uncentered pair common image is eventually exactly one fixed continuum mode.

Thus centered convergence is reduced to:

~~~text
OS-vacuum pair common image
+
pair-top common image.
~~~

### #5072

The canonical-sign OS-vacuum pair common image is exactly constant one at every scale.

Therefore the centered common image already converges.

### #5073

For unit top images:

~~~text
top image -> 1 strongly
  iff
finite vacuum/top overlap -> 1.
~~~

This is valid but stronger than needed.

### #5074

Generic Hilbert lemma:

~~~text
c_n -> c,
||t_n|| = 1,
<t_n,c_n> -> 0
  ->
c_n - <t_n,c_n> t_n -> c.
~~~

Therefore the only needed scalar input is:

~~~text
local projected-top coefficient -> 0.
~~~

No convergence of the moving top direction is required.

Status: CLOSED REDUCTION.

---

## 10. Positive-half factorization of the local coefficient — #5075/#5076

### #5075

For arbitrary physical one-slice x,y:

~~~text
<v_OS, x tensor y>
  =
<v_OS, omega tensor omega>
  *
<S_half x, y>.
~~~

This is exact and normalization free.

No H1-D5 or vacuum alignment is used.

### #5076

For the explicit two-mode pair f_k tensor 1:

~~~text
a_k
  =
alpha_k * delta
  -
gamma^2 * m_k,
~~~

where

~~~text
alpha_k = <omega, f_k>,
delta   = <omega, 1>,
gamma   = <v_OS, omega tensor omega>,
m_k     = <S_half f_k, 1>.
~~~

This converts the pair-Haar local coefficient into one-slice data.

Status: CLOSED.

Interpretation:

The old conditional route could try to control the excitation part of m_k by q0 and separately control the fidelity defect involving gamma.

That route remains available, but it is no longer preferred because #5077 opens a cleaner finite-dimensional construction.

---

## 11. #5077 — all SU(2) Gram--Schmidt Wilson modes are physical pairs

File:

~~~text
MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean
~~~

PR #5077 proves, for every SU(2) Wilson-energy Gram--Schmidt mode k:

1. the primary spatial plaquette continuous observable is defined explicitly;
2. it is gauge invariant;
3. it gives a physical one-slice L2 vector;
4. the ordered endpoint-pair boundary realization is exactly decomposable;
5. the pair belongs to the completed physical pair carrier;
6. the whole endpoint-pair family is orthonormal in pair Haar L2.

Schematically:

~~~text
u_k,n in PhysicalPairCarrier

<u_i,n, u_j,n> = delta_ij.
~~~

This is the key new kinematic resource.

Status: CLOSED.

---

## 12. #5078 — pure three-mode two-functional selector CLOSED

PR #5078 proves the finite-dimensional theorem independently of the Yang--Mills model.

File:

~~~text
MGAP4D/MathlibAnalytic/RealEuclideanFinThreeTwoFunctionalKernel.lean
~~~

Input:

~~~text
two real linear functionals
  ell_0, ell_1
on
  EuclideanSpace R (Fin 3).
~~~

Output:

~~~text
exists c,
||c|| = 1,
ell_0(c) = 0,
ell_1(c) = 0.
~~~

The proof uses pinned-mathlib rank-nullity through:

~~~text
LinearMap.ker_ne_bot_of_finrank_lt
~~~

and normalizes a nonzero common-kernel vector.

Status: CLOSED.

### 12.1 Immediate model-facing instantiation

Use the first three #5077 physical pair modes:

~~~text
u_0,n
u_1,n
u_2,n.
~~~

Define the synthesis

~~~text
Syn_n(c)
  =
sum k : Fin 3, c_k * u_k,n.
~~~

Prove from #5077 orthonormality:

~~~text
||Syn_n(c)|| = ||c||.
~~~

Define the two functionals required by #5078:

~~~text
Vac_n(c)
  =
<v_OS,n, Syn_n(c)>

Top_n(c)
  =
<Omega_pair,n, Syn_n(c)>.
~~~

Apply #5078 to obtain c_n with

~~~text
||c_n|| = 1
Vac_n(c_n) = 0
Top_n(c_n) = 0.
~~~

Set

~~~text
x_n = Syn_n(c_n).
~~~

Target finite package:

~~~text
||x_n|| = 1
<v_OS,n,x_n> = 0
<Omega_pair,n,x_n> = 0
x_n in PhysicalPairCarrier
x_n in PairNonTop
||S_pair,n^m x_n|| <= q0^m.
~~~

Because the vacuum pairing is zero, finite vacuum-centering leaves x_n unchanged.

Because pair TopTop is one-dimensional, pair-top scalar orthogonality gives exact non-top membership.

This is now the immediate theorem target.

## 13. Projective limit of the scale-dependent three-mode selector

The coefficient vector now depends on scale.

So fixed-label projective coherence alone is not sufficient.

However:

~~~text
||ĉ_n|| = 1
~~~

places every coefficient vector on the compact unit sphere in R^3.

### 13.1 coefficient subsequence

Use finite-dimensional compactness / Bolzano--Weierstrass to obtain:

~~~text
exists phi : N -> N,
StrictMono phi,
ĉ_(phi j) -> c_infinity,
||c_infinity|| = 1.
~~~

Pinned mathlib contains sequence compactness tools such as:

~~~text
IsSeqCompact
tendsto_subseq_of_bounded
~~~

Either route is acceptable.

### 13.2 coherent continuum modes

The existing SU(2) Gram--Schmidt cylinder/readout machinery gives a fixed continuum projective mode U_k for every fixed k.

Use only k = 0,1,2.

### 13.3 synthesis convergence

Show:

~~~text
Embed(x_(phi j))
  =
sum k<3, ĉ_(phi j,k) U_k
~~~

eventually / exactly at containing scales.

Then continuity of finite sums gives:

~~~text
Embed(x_(phi j))
  ->
y =
sum k<3, c_infinity,k U_k.
~~~

### 13.4 nonzero limit

Because U_0,U_1,U_2 are orthonormal and ||c_infinity|| = 1:

~~~text
||y|| = 1.
~~~

Thus:

~~~text
y != 0.
~~~

This should give the cleanest current nonzero projective initial excitation.

---

## 14. Why three modes are preferable to two

With two modes one can always solve one scalar top-orthogonality equation.

But after vacuum centering, the selected one-dimensional kernel can in principle coincide with a vacuum direction and collapse to zero.

Three modes allow two exact scalar conditions simultaneously:

~~~text
vacuum pairing = 0
pair-top pairing = 0.
~~~

The remaining kernel still has dimension at least one.

Therefore nonzero norm can be guaranteed before centering.

This is the dimensional reason for the #5077 extension from two modes to the full Gram--Schmidt family.

---

## 15. Relation to #5074--#5076

The local coefficient route remains mathematically correct.

It is useful for:

- diagnostics;
- quantitative estimates;
- comparing fixed-mode and moving-combination approaches;
- possible later bounds on selected coefficient families.

But the three-mode kernel route should not require:

~~~text
gamma_n -> 1
~~~

or any equivalent global vacuum/top fidelity statement.

If the three-mode route closes cleanly, #5074--#5076 become supporting structure rather than the main seam.

---

## 16. H1-C3: evolved projective dynamics remains open

Even after a nonzero initial strong limit y is built, one still needs the evolved states.

For fixed natural time m define finite evolved states:

~~~text
z_n,m = S_pair,n^m x_n.
~~~

Known:

~~~text
||z_n,m|| <= q0^m.
~~~

Unknown:

- do the z_n,m have coherent projective images?
- do they have strong limits along the same subsequence?
- are the limits compatible in m?
- do they define one bounded operator T on the continuum excitation space?
- is T symmetric/self-adjoint in the required sense?

Target:

~~~text
Embed(z_n,m) -> T^m y

and

||T^m y|| <= q0^m ||y||.
~~~

This is the next genuinely dynamical bridge.

---

## 17. Do not overclaim from finite q0

The statement

~~~text
||S_n^m x_n|| <= q0^m
~~~

is a finite discrete-time estimate.

It does not yet prove:

- existence of a continuum transfer operator;
- strong continuity in physical time;
- a continuum Hamiltonian;
- a positive physical mass.

Every README / paper statement must preserve this distinction.

---

## 18. H2: spacing-scaled physical time

If lattice spacing a_n tends to zero, a fixed q0 gives

~~~text
q0^floor(t/a_n) -> 0
~~~

for every fixed t > 0.

Therefore q0 by itself corresponds to instantaneous collapse under naive physical-time scaling.

A nontrivial physical semigroup requires a scale-sensitive rate, for example:

~~~text
q_n =
exp(-m_n a_n + o(a_n)).
~~~

Equivalent formulations may use:

- transfer logarithms;
- rescaled Dirichlet forms;
- Poincare inequalities;
- generator lower bounds.

Existing repository modules for physical-time rate extraction should be used only after H1-C3 produces actual continuum dynamics.

---

## 19. H3: OS reconstruction

After H1/H2 produce model data, required output is:

- continuum physical Hilbert space;
- normalized vacuum;
- strongly continuous contraction semigroup;
- symmetry / self-adjointness;
- closed Hamiltonian;
- identified vacuum-orthogonal excitation sector.

Much generic functional analysis is already formalized.

The remaining issue is model-facing input.

---

## 20. H4: spectral / Wightman mass gap

Final intended route:

~~~text
finite coercivity
  ->
finite exact non-top excitation
  ->
nonzero projective strong limit
  ->
projective evolved dynamics
  ->
physical-time scaling
  ->
OS Hamiltonian
  ->
spectral lower bound above vacuum
  ->
Wightman / energy-momentum mass gap.
~~~

No current theorem claims the final step is complete.

---

## 21. Lean implementation guidance

Repository-specific lessons to preserve:

### Exact environment

Use:

~~~text
Lean v4.30.0-rc2
mathlib 5450b53e5ddc75d46418fabb605edbf36bd0beb6
~~~

Current-master theorem names are only hints.

Pinned mathlib is authoritative.

### Full-file audit

When CI fails:

- inspect every error in the changed file;
- do not patch only the first line;
- inspect neighboring theorem signatures;
- identify whether failure is mathematical, coercional, or elaborational.

### Section variables

Lean resolves theorem headers before processing the proof body.

If a section parameter does not occur in a result type strongly enough to infer it, pass it explicitly:

~~~text
(halfExtent := halfExtent)
~~~

### Rewriting through coercions

If rw cannot see the intended occurrence:

- prefer exact theorem terms;
- prefer simpa only using;
- expose the exact coercion boundary;
- avoid relying on pretty-printed syntactic similarity.

### Definitional aliases

Avoid brittle change when crossing several named aliases.

Prefer:

- unfold the exact wrapper definitions;
- then apply the core theorem.

### CI

For theorem-bearing PRs:

- require exact-head PR Lean Fast Check success;
- require matching exact-head receipt success.

For docs-only PRs:

- do not rerun strict Lean merely because README / ROADMAP changed.

---

## 22. Recent milestone ledger

| PR | Status | Main result |
| --- | --- | --- |
| #5029 | merged | independent gauge-fixed pair sector = physical pair carrier |
| #5038 | merged | H1-D5 forces one-slab power identity |
| #5041 | merged | H1-D5 forces rank-one normalized transfer |
| #5045 | merged | two-mode feature-kernel obstruction |
| #5058 | merged | positive-coupling strict bare crossing Gram |
| #5059 | merged | continuous SU(2) two-mode span = span{1,r} |
| #5061 | merged | completed H1-D5 no-go |
| #5063 | merged | centered-pair scalar replacement |
| #5064 | merged | old vacuum/top alignment route excluded |
| #5065 | merged | canonical projected physical non-top excitation |
| #5066 | merged | projected nonzero reduced to vacuum/top overlap |
| #5067 | merged | finite projected excitation nonzero |
| #5068 | merged | common projective embedding |
| #5069 | merged | fixed nonzero mode on infinite subsequence |
| #5070 | merged | projected strong-convergence factorization |
| #5071 | merged | centered convergence reduced to vacuum/top common images |
| #5072 | merged | OS vacuum pair common image = constant one |
| #5073 | merged | pair-top convergence iff vacuum/top overlap -> 1 |
| #5074 | merged | local top-coefficient criterion |
| #5075 | merged | OS-vacuum coefficient factorization through normalized half transfer |
| #5076 | merged | exact one-slice local top coefficient formula |
| #5077 | merged | all SU(2) Gram--Schmidt modes realized as physical orthonormal endpoint pairs |
| #5078 | merged | abstract Euclidean Fin 3 two-functional unit-kernel selector |

---

## 23. Immediate implementation sequence

### G1 — three-mode synthesis

Create the finite linear synthesis of the first three #5077 pair modes and prove its norm formula from orthonormality.

### G2 — instantiate #5078

Define the vacuum-pairing and pair-top-pairing linear functionals on Euclidean Fin 3 and feed them directly to RealEuclideanFinThreeTwoFunctionalKernel.

### G3 — exact finite non-top unit excitation

Synthesize x_n and prove:

~~~text
||x_n|| = 1
<v_OS,n,x_n> = 0
<Omega_pair,n,x_n> = 0
x_n in PhysicalPairCarrier
x_n in PairNonTop.
~~~

### G4 — q0 receipt

Apply the existing completed pair non-top power theorem:

~~~text
||S_pair,n^m x_n|| <= q0^m.
~~~

### G5 — coefficient compactness

Extract a convergent unit coefficient subsequence in R^3.

### G6 — projective synthesis convergence

Transport the three fixed coherent Gram--Schmidt modes and show the selected combinations converge strongly.

### G7 — nonzero continuum excitation

Prove the limit has norm one.

### G8 — evolved projective coherence

Begin H1-C3 with the same selected subsequence.

This is the preferred next formalization order.

---

## 24. Restart instructions

Freshly re-observe:

~~~text
formal/real-hilbert-uniform-coercive-strong-limit
~~~

Then inspect:

1. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical.lean
2. MGAP4D/MathlibAnalytic/RealEuclideanFinThreeTwoFunctionalKernel.lean
3. MGAP4D/MathlibAnalytic/SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt.lean
4. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCylinder.lean
5. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadout.lean
6. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedProjectedLocalTopCoefficientCriterion.lean
7. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedPairPositiveHalfTransferRatio.lean
8. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonVacuumNormalizedLocalTopOneSliceFormula.lean
9. the full completed physical pair non-top q0 power-decay theorem from #5006.

Current handoff:

~~~text
CLOSED:
  finite q0
  full completed pair non-top q0
  top and pair-top simplicity
  H1-D4
  completed H1-D5 no-go
  finite nonzero projected excitation
  projective embedding
  vacuum common image = one
  local coefficient criterion
  half-transfer/local coefficient factorization
  infinite SU(2) Gram--Schmidt physical orthonormal pair family

NEXT:
  instantiate #5078 on the three #5077 pair modes
  ->
  unit exact non-top pair at every scale
  ->
  q0
  ->
  coefficient compactness
  ->
  nonzero projective strong limit

THEN:
  evolved projective dynamics

THEN:
  physical-time scaling

LATER:
  OS Hamiltonian
  spectral / Wightman mass gap.
~~~
