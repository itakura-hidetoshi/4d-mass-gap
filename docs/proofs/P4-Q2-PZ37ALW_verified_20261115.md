# P4-Q2-PZ37ALW — original fixed-beta0 Wilson raw moment-step bridge

2026-11-15 JST. [Theorem PR #6761](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6761) **MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit`, canonical squash `2760ea8269b03a1e712306fdd8643de15bcc7137`.

## Exact physical scope

One new append-only Lean4 leaf (212 physical source lines including terminator, 8 independently audited declarations):

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0RawWilsonMomentStepBridgeV5_PZ37ALW.lean`

Original SU(2) Wilson physical operators `P_H`, normalized top-orthogonal restrictions `R_H`, true top sectors `K_H`, Haar/AJA source, and fixed prescribed `beta0=log(3/2)/64` are unchanged. ALN already formally certifies the genuinely physical positive ALJ moment normalizer floor `0<F_H<=||P_H||`. ALV already defines `Q_H=||R_H(beta0)||²` and proves the positive-part deficit loss `L_H=max(0,Q_(H+1)-Q_H)`.

ALW adds an **explicit typed physical raw-moment input** at volume H+1:

```text
b_H >= 0;
for every x in the true physical K_(H+1),
 ||P_(H+1) x|| <= sqrt(Q_H+b_H) * F_(H+1) * ||x||.
```

Under this independent input (NOT claimed to hold), the existing ALN true-physical raw-to-normalized moment lemma implies `||R_(H+1)||<=sqrt(Q_H+b_H)`; a fully typed norm square transport yields `Q_(H+1)<=Q_H+b_H` and `L_H<=b_H`. A separate formulation accepts a sector-wide raw scalar ceiling `a_H` and the stronger independent normalizer comparison `a_H<=sqrt(Q_H+b_H)*F_(H+1)`.

With raw physical certificates at all H, `b_H>=0` and independently proved `forall H, sum_{i<H}b_i<=B<delta_0`, ALU produces a positive uniform fixed-beta0 gap `(delta_0-B)/2`. Geometric `b_H=C*r^H`, `0<=r<1`, `C<(1-r)*delta_0` is another conditional route, and a tail-only geometric version beyond finite M uses ALT's unconditional finite-prefix positivity. A separate obstruction theorem says if the actual next volume scalar `Q_(H+1)>Q_H+b`, the associated raw moment step certificate cannot hold.

**Strong-premise warning:** The ALJ `F_H` is a physical *lower* bound on `||P_H||` and may be much smaller; therefore this raw physical estimate is strictly stronger than the normalized scalar ALV step premise, not equivalent to it. Generic operator-norm domination `||P_H x||<=||P_H||*||x||` does NOT prove it.

**OPEN / NO_DATA:** No true original Wilson kernel estimate proving the raw step certificate, sector ceiling, numerical geometric constants, small summable total budget, or all-H fixed-beta0 physical gap has been supplied. No Hamiltonian or continuum four-dimensional Yang–Mills mass gap is inferred.

## Exact-source Lean4 verification and repair provenance

Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

- Initial source `f0f373950df123f61d228a58f2d4ecea2be4611d`, [CI #43648058023](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43648058023) FAILURE: one direct elaboration type mismatch from using `sq_le_sq₀.mp` in the wrong logical direction.
- Intermediate `103580c20cb018b2565a3309cb12645daa45b896`, [CI #43648453368](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43648453368) FAILURE: `sq_le_sq₀.mpr` was the right direction, but the abbreviation `Q(H+1)` hid the typed norm needed by the implicit argument elaborator.
- Intermediate `664101ab75ac5196983b4a57c8295335591557e3`, [CI #43649006157](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43649006157) FAILURE: repeated large physical operator types still left the generic norm parameters underconstrained.
- Intermediate `e15943ff9e7548e739effe3a82c5ed6bb79ea497`, [CI #43649468497](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43649468497) FAILURE: duplicating a dependent-typed `R_(H+1)` in a `norm_nonneg` argument caused fixed-Lean `SeminormedAddGroup` typeclass timeout.
- Final repaired source `14c07266dc45fbf330550e962fe463889310eac9` shares a single local fully typed `Rnext`, uses `mul_self_le_mul_self` and real arithmetic `nlinarith only [hMul, Real.sq_sqrt hq]`. No extra axioms, sorry, weakened theorems or increased heartbeat limits. File blob `e992611b05ad50922e90f99d5c18513f28d18bea`.
- Final [exact-source CI #43649964065](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43649964065) **completed/SUCCESS**, pinned Lean **11,487/11,487**, **8/8** actual `#print axioms` restricted to `propext`, `Classical.choice`, `Quot.sound`, ALW `sorryAx` absent, changed ALW warning/error **0/0**. Changed Lean job `132616001171` and independent receipt job `132617296598` completed SUCCESS. Exact observed PR receipt: `[mcp-receipt] event=pull_request exact_sha=14c07266dc45fbf330550e962fe463889310eac9 source_result=success run=43649964065 attempt=1`.
- Source/synthetic test-merge/canonical squash Git tree **identical**: `b3065d6a5cd663c8f16136489ad4a48c86646d73`.
- Independent canonical formal [push CI #43650478333](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43650478333) was **in progress at initial record creation**. Append its verified outcome only after direct observation of workflow, job and exact-head receipt. Do not treat the successful PR CI as its result.

All changes append-only / tighten-only / overwrite-forbidden / same-root. No existing proof, Wilson action, root import, toolchain, manifest or workflow was modified.

## Next physical research step

Construct original-beta0 SU(2) Wilson excited-sector upper bounds together with **separate physical full operator normalizer lower bounds**, and prove the needed volume-step comparison without identifying incompatible `H`-dependent Hilbert carriers. A closer normalizer bound may be required because the existing ALJ moment floor can be too weak for this sufficient test. The exact sharp-sqrt gap from a uniform squared-norm budget is a separate formal refinement; neither it nor conditional ALW asserts an actual Wilson mass-gap proof.


## Independent canonical formal push certification — completed (2026-11-15 JST)

The preceding push CI PENDING record reflects the correct status at initial source-writing time. GitHub MCP has independently reobserved [push CI #43650478333](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43650478333) **completed/SUCCESS**, triggered by **event=push** for the EXACT authoritative canonical formal HEAD `2760ea8269b03a1e712306fdd8643de15bcc7137`.

The actual pinned Lean full dependency closure **11,487/11,487** completed SUCCESS, all 8/8 ALW `#print axioms` are exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` in the new audited declarations and no ALW warnings/errors. Changed-Lean job `132617591073` completed SUCCESS and independent receipt job `132618904816` completed SUCCESS, with the actually observed exact-head completion log:

```text
[mcp-receipt] event=push exact_sha=2760ea8269b03a1e712306fdd8643de15bcc7137 source_result=success run=43650478333 attempt=1
```

The actual source/test-merge/squash tree remains `b3065d6a5cd663c8f16136489ad4a48c86646d73`. This machine result certifies ALW's **conditional** physical Wilson raw-moment step bridge, not the still-unproved genuine raw premise, summable volume-loss budget, original-beta0 uniform gap or continuum Yang–Mills mass gap.
