# C5 Cross-Boundary One-Way Tagged Carrier Design

**Repository:** `itakura-hidetoshi/4d-mass-gap`

**Canonical base:** `ba063aec4cd8f17383c6f5b347ebb334e3886061`

**Working branch:** `formal/c5-cross-boundary-one-way-tagged-carrier-v1`

## Goal

Represent the already-proved C5 right-source to left-target cross-boundary influence as a genuine off-diagonal finite influence kernel without falsely asserting the reverse direction.

## Mathematical context

The current cross-boundary majorant has a single surviving scalar coefficient

\[
q(\beta)=2\frac{e^{16\beta}-1}{e^{16\beta}+1},
\]

with the canonical theorem unit establishing

\[
0\le \beta \Longrightarrow q(\beta)\ge 0,
\]

\[
\beta<\frac{\log 3}{16}\Longrightarrow q(\beta)<1,
\]

and pointwise contraction for unit-bounded source profiles.

The generic carrier `FiniteNonnegativeInfluenceKernelData ι` requires global diagonal zero:

```lean
influence_diagonal_zero : ∀ e : ι, influence e e = 0
```

Using the same spatial-link index for both boundary copies would therefore incorrectly force the physically meaningful matching-coordinate cross-boundary influence onto the carrier diagonal.

## Index design

Use the disjoint tagged union

```lean
Sum
  (PeriodicHypercubicEvenSpatialSliceLink H)
  (PeriodicHypercubicEvenSpatialSliceLink H)
```

with the convention

- `Sum.inl fiber` = left target copy,
- `Sum.inr source` = right source copy.

Because `Sum.inl e ≠ Sum.inr e`, matching spatial coordinates across the boundary are genuine off-diagonal global indices.

No additional boundary-side structure is introduced. `Sum` is sufficient and keeps the theorem unit minimal.

## One-way influence semantics

Define a tagged influence function by cases:

```lean
fun target source =>
  match target, source with
  | Sum.inl fiber, Sum.inr source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source
  | _, _ => 0
```

This is intentionally a **one-way carrier**. The three omitted blocks are zero because they are outside the current theorem carrier, not because a physical reverse-influence vanishing theorem has been proved.

In particular,

```lean
influence (Sum.inr _) (Sum.inl _) = 0
```

must not be documented or used as a physical reciprocity statement.

## Required theorem unit

The new Lean file should prove, in this order:

1. the tagged influence is nonnegative when `0 ≤ beta`;
2. the associated `FiniteNonnegativeInfluenceKernelData` exists;
3. global diagonal zero holds structurally from the disjoint `Sum` tags;
4. the left-target/right-source block is exactly the existing C5 bounded-test majorant;
5. all other tagged blocks are zero by definition of this one-way carrier;
6. the left-target row sum reduces exactly to the single scalar contraction coefficient `q(beta)`;
7. in the small-coupling regime `0 ≤ beta < log 3 / 16`, that left-target row sum is strictly `< 1`.

The row theorem must not introduce a spatial-volume factor.

## File boundary

Create one focused file:

`MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedCarrier.lean`

It should import the existing cross-boundary influence-operator file that already contains the named scalar coefficient and its contraction theorem unit.

Do not modify earlier mathematical carrier files unless elaboration demonstrates an actual dependency requirement.

## Testing and authority

Development follows RED → GREEN Lean elaboration. Every theorem-bearing commit must be checked by `PR Lean Fast Check` on the exact head SHA before any merge decision.

Authority order remains:

1. exact GitHub canonical SHA;
2. formal Lean artifacts;
3. README / ROADMAP;
4. CI/runtime receipts;
5. history / memory.

The authoritative theorem-carrier branch remains `formal/real-hilbert-uniform-coercive-strong-limit`. `main` is not theorem authority.

## Non-goals

This unit does not prove reverse left-source to right-target influence, bidirectional Dobrushin contraction, reciprocity, symmetry of the tagged kernel, spectral-radius contraction of a two-way operator, or any new physical assumption.

Those require separate theorem units and separate evidence.
