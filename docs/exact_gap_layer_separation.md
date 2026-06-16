# Exact-gap layer separation

**Updated:** 2026-06-17

This note records the dependency-level meaning of the normalized exact-gap carrier. It replaces the older reading that focused only on whether the literal `33/20` appeared in `Basic.lean` or `ExactGapReal.lean`.

## Central rule

```text
The literal 33/20 enters the source tree in
HamiltonianPVMSpectralExactGapValue.lean.

ExactGapReal.lean projects a carrier from that package.

Later spectral, R6, R7, and terminal files align and transport the same value.

Therefore, local absence of the literal in ExactGapReal.lean is not an
independent physical derivation of 33/20.
```

The concrete finite Wilson heat-bath lane is a separate construction lane. Its current results do not yet identify a physical Yang--Mills Hamiltonian gap with the internal normalized carrier.

---

## Current dependency layers

### Layer 0 — Basic route marker

File:

```text
MGAP4D/MathlibAnalytic/Basic.lean
```

Role:

- records route and review markers;
- does not provide the finite Wilson heat-bath construction;
- does not independently construct a physical Hamiltonian;
- is not the source of the numerical literal.

### Layer 1 — Numerical origin package

File:

```text
MGAP4D/MathlibAnalytic/HamiltonianPVMSpectralExactGapValue.lean
```

This file defines

```lean
def hamiltonianPVMSpectralNormalized3320Value : Real :=
  (33 : Real) / 20
```

and constructs `HamiltonianPVMSpectralExactGapValueOrigin` with fields shaped as Hamiltonian energy, spectral support, a PVM-visible window, spectral weight, and a normalization equality.

The installed witness uses:

```text
hamiltonianCarrier       = Nat -> Real
distinguishedState       = zero function
hamiltonianEnergy        = constant 33/20
spectralSupport          = [33/20, infinity)
pvmSpectralWindow        = the same support ray
spectralWeight           = constant 1
```

This is a valid Lean witness for the declared structure. It is not, by itself, a construction of the physical four-dimensional Yang--Mills Hilbert space or Hamiltonian.

### Layer 2 — Public carrier projection

File:

```text
MGAP4D/MathlibAnalytic/ExactGapReal.lean
```

The carrier is defined by

```lean
def exactGapValueReal : Real :=
  hamiltonianPVMSpectralExactGapValue
```

This file proves positivity, the above-one property, support membership, lower-bound statements, and positive/nonzero weight for the projected package.

Correct reading:

```text
ExactGapReal.lean does not contain a local closed-form assignment to 33/20,
but its dependency already carries 33/20.
```

Thus the file boundary provides syntactic and API separation, not semantic independence from the chosen normalized value.

### Layer 3 — Spectral and R6/R7 transport

Representative files:

```text
MGAP4D/MathlibAnalytic/YangMillsHamiltonianSpectralDerivation3320.lean
MGAP4D/R6/Theorem/ExactAtom3320NonDefinitionalDerivation.lean
MGAP4D/R7/Theorem.lean
MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean
```

These layers:

- align `exactGapValueReal` with a derived-value field;
- preserve support and positive-weight statements;
- export equality with `33/20` at later audit layers;
- carry public-boundary and release markers.

They do not erase the dependency on Layer 1. Transport through a spectral/PVM-shaped interface is not an independent derivation when the transported value was already fixed in the origin package.

### Layer 4 — Concrete finite Wilson heat-bath construction

Representative files:

```text
FiniteLatticeWilsonGibbsRealExpectation.lean
FiniteLatticeWilsonSingleLinkHeatBathDirichlet.lean
FiniteLatticeWilsonSingleLinkHeatBathProjection.lean
FiniteLatticeWilsonSingleLinkHeatBathFluctuationProjection.lean
FiniteLatticeWilsonSingleLinkHeatBathFluctuationEnergy.lean
FiniteLatticeWilsonSingleLinkHeatBathDetailedBalance.lean
FiniteWilsonHeatBathForwardSumExplicit.lean
```

This lane is constructed from actual finite Wilson Gibbs weights. It currently supplies:

- Gibbs and conditional variances;
- the heat-bath Dirichlet form;
- `P_e` and `Q_e` projection algebra;
- local fluctuation-energy identities;
- detailed balance;
- the reversible product-sum identity.

This lane is mathematically more concrete than the normalized audit carrier, but it has not yet derived the physical normalized gap.

### Layer 5 — Missing physical identification

The following remain open:

- a scale-uniform estimate for the actual non-Abelian Wilson conditional laws;
- a theorem converting Dobrushin data into the required operator contraction;
- a consistent scale bridge from the heat-bath generator to the transfer Hamiltonian;
- construction of the physical Hilbert space and Hamiltonian independently of `33/20`;
- derivation of the lowest nonzero spectral value;
- a nontrivial regular continuum limit;
- independent external review.

Only after these are closed can an exact physical value be assessed as a derived theorem rather than an internal normalization.

---

## Local separation versus semantic separation

| Question | Answer |
|---|---|
| Is `33/20` written in `Basic.lean`? | No |
| Is `33/20` written directly in `ExactGapReal.lean`? | No |
| Does a dependency of `ExactGapReal.lean` define `33/20`? | Yes |
| Is `exactGapValueReal` projected from that dependency? | Yes |
| Do R6/R7 transport the projected value? | Yes |
| Is a physical Yang--Mills Hamiltonian first constructed independently and then shown to have that gap? | Not yet |

The correct review unit is the full dependency graph, not one file in isolation.

---

## Random-scan scale mismatch

The current random-scan contraction structures require

```text
0 <= rho
rho < 1
exactGapValueReal <= 1 - rho.
```

The carrier layer proves

```text
1 < exactGapValueReal.
```

Hence

```text
0 <= rho
  -> 1 - rho <= 1
  -> 1 - rho < exactGapValueReal,
```

which contradicts `exactGapValueReal <= 1 - rho`.

Affected interfaces include the finite and uniform sweep/random-scan exact-gap data structures.

This shows that the heat-bath Markov gap and the normalized physical gap are currently being placed on incompatible scales.

A corrected separation should use distinct quantities:

```text
lambda_HB    = heat-bath or Markov coercivity constant
Delta_norm   = normalized physical Hamiltonian gap
s_HB > 0     = explicit time/energy conversion scale

lambda_HB <= 1 - rho
Delta_norm = s_HB * lambda_HB.
```

Alternatively, use the continuous-time generator `sum_e (I - P_e)` and prove its relation to the transfer Hamiltonian with an explicit normalization.

---

## Reviewer checklist

1. Start with `HamiltonianPVMSpectralExactGapValue.lean`, not only `ExactGapReal.lean`.
2. Inspect the concrete witness used to prove existence of the origin package.
3. Distinguish a chosen normalization from a spectral value derived from a physical operator.
4. Trace every later `33/20` theorem back to its dependency source.
5. Review the finite Wilson heat-bath lane separately from the normalized audit lane.
6. Check whether every conditional bridge has an actually constructed input.
7. Repair the random-scan normalization before treating it as a route to the normalized physical gap.
8. Require a physical Hamiltonian construction independent of the target number.

---

## Current public wording

Use:

```text
The repository contains an internal normalized 33/20 carrier transported
through Hamiltonian/PVM/spectral-shaped audit interfaces. The current
dependency graph initializes that normalization before the later transport
steps. The concrete finite Wilson heat-bath lane and conditional continuum
bridges are substantial formal developments, but an independent physical
derivation of the four-dimensional Yang--Mills mass gap and of the exact value
33/20 remains open.
```

Do not use:

```text
ExactGapReal.lean derives 33/20 from the physical Yang--Mills spectrum.
R6 independently proves the number from a previously constructed Hamiltonian.
The random-scan contraction already yields the normalized physical gap.
The repository is a completed public solution of the mass-gap problem.
```

The Lean source tree remains authoritative, and claims must be evaluated across the complete dependency graph.
