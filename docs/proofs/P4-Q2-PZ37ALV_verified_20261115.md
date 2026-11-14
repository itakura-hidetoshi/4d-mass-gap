# P4-Q2-PZ37ALV — genuine original fixed-beta0 Wilson scalar geometric volume-step criterion

2026-11-15 JST. [Theorem PR #6758](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6758) **MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit` at canonical commit `7b33f85634aae0a93f2d4665336a2df4359f3b6a`.

## Exact model, proof scope and obstruction

One new append-only Lean leaf (219 added lines, 8 audited declarations):

`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0GeometricVolumeStepNormBudgetV5_PZ37ALV.lean`

The original SU(2) Wilson physical transfer operator, its normalization, fixed physical coupling `beta0=log(3/2)/64`, original Haar/AJA data and top-sector orthogonal carriers are **unchanged**. Different volumes `H` have different Hilbert spaces, so this file never forms `R_(H+1)-R_H` as an operator difference. The comparable scalar is the true norm square:

```text
n_H := ||R_H(beta0)||^2;  delta_H := 1-n_H > 0.
L_H := max(delta_H-delta_(H+1),0)
     = max(n_(H+1)-n_H,0).
```

The last equality is an unconditional Lean theorem for the actual fixed-beta0 physical scalar norms. The finite geometric sum identity and bound are proved algebraically.

### Geometric step condition (NOT YET PROVED for Wilson physics)

Assume an **independently established physical estimate** for one common `C,r`, chosen before all volumes:

```text
0 <= C, 0 <= r < 1,
n_(H+1) <= n_H + C*r^H  for every H,
C < (1-r)*delta_0.
```

ALV and the already certified ALU telescoping theorem yield the **CONDITIONAL** uniform gap:

```text
gap_H(beta0) >= (delta_0-C/(1-r))/2 > 0
for every finite H.
```

The separate **finite-prefix/tail refinement** is weaker in volume scope. For a selected finite `M`, ALT proves positivity through `H<=M` without extra premises. If only for the tail there exist `C,r` with `0<=C`, `0<=r<1`, `C<(1-r)*delta_M`, and

```text
n_(M+k+1) <= n_(M+k) + C*r^k   for every k,
```

then a common all-H positive gap exists. Its certificate takes the minimum of ALT's positive finite-prefix gap and `(delta_M-C/(1-r))/2`.

**OPEN physical input / NO_DATA:** No Wilson-specific decay constants `C,r` or true one-volume excited spectral-norm increment upper estimate are constructed in this leaf, and existing high-temperature coercivity cannot simply be transferred to the original fixed beta0, which is outside the existing AKL cutoff. These conditional sufficient criteria do **not** prove the all-volume original-beta0 spectral gap, a Hamiltonian mass gap, or the continuum four-dimensional Yang-Mills mass gap.

## Reproducible exact-source machine certificate

- Source parent: `06340f4d92547f4a0b42b7350278c7ccbffdae25` (ALU verified formal record integrated).
- Source commit `f018d4250be2333bed281bde357e9ce82d297d72`.
- Source file Git blob `dd28f710b672d033256cd92bb44d20eae75de7a2`.
- Canonical MERGED squash `7b33f85634aae0a93f2d4665336a2df4359f3b6a`.
- Source/test-merge/canonical commit Git tree **identical**: `2ba386aef10da531805bb20be2e965a9b0cc5128`.
- [Exact-source PR CI #43643045960](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43643045960): **completed/SUCCESS**, pinned Lean dependency closure **11,486/11,486**, 8/8 actual ALV `#print axioms` lines depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` in ALV audits and no changed-source warning/error. Changed Lean job `132594623473` completed/SUCCESS; exact-head MCP completion receipt job `132596428360` completed/SUCCESS.
- Lean pin: `v4.30.0-rc2`. mathlib pin: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Independent authoritative post-merge [push CI #43643707032](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43643707032): **in progress at the initial creation of this record**. An independent completion receipt must be appended only after observing that run completed.

No existing proof, root import, physics implementation, workflow or pinned dependency was overwritten. Append-only / tighten-only / overwrite-forbidden / same-root.

## Next research step

Derive the required *genuine* original fixed-beta0 Wilson two-volume scalar excited-norm estimates. Candidate methods include independently verified finite-size correlation/locality, an appropriately typed inter-volume comparison, or a model-specific kernel estimate that avoids cross-carrier subtraction; none is presently certified by ALV. A finite-prefix calculation alone cannot establish the geometric tail hypothesis. Obstruction remains explicit.
