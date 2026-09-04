import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarInnerPair
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfOuterInnerDeepIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfOuterInnerDeepCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfOuterInnerDeepSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfOuterInnerDeepMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfOuterInnerDeepBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfOuterInnerDeepSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

/-- Haar law on the complete nondegenerate positive-half path after exposing,
in order, the outer boundary pair, the two distinct inward boundary slices, and
the remaining deeper interior.

The association is deliberately
`outerPair × (innerPair × deep)` so the first two factors line up directly with
the ambient pair-Haar one-slab transfer kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure
    (M N : ℕ) :
    Measure
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N)) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N).prod
    ((periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N).prod
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPathHaarMeasure M N))

instance
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaar_isProbabilityMeasure
    (M N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure
  infer_instance

/-- For `H = M + 2`, compose the canonical outer-boundary split with the
canonical strict-interior inner-pair split.

Thus a complete path is represented as
`outerPair × (innerPair × deep)` without any proof-dependent cast and without
introducing a false independent pair in the `H = 1` diagonal geometry. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
    (M N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N ≃ᵐ
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
        ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N)) :=
  let Outer :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let outer :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N
  let inner :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N
  outer.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Outer) inner)

/-- Exact three-factor finite-product Haar decomposition for every nondegenerate
positive half-cylinder `H = M + 2`:

`complete path Haar = outer pair-Haar × (inner pair-Haar × deep Haar)`.

This is the Fubini form needed to integrate the pointwise Markov factorization
against independent outer and inner pair variables before handling the deeper
interior. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv_measurePreserving
    (M N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
        M N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
  let Outer :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N
  let μOuter :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (M + 2) N
  let outer :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv
      (M + 2) N
  let inner :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv
      M N
  let refine := MeasurableEquiv.prodCongr (MeasurableEquiv.refl Outer) inner

  have hOuter :
      MeasurePreserving outer
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
          (M + 2) N) := by
    simpa [outer] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathBoundaryInteriorMeasurableEquiv_measurePreserving
        (M + 2) N)

  have hInner :
      MeasurePreserving inner
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathHaarMeasure
          (M + 2) N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure
          M N) := by
    simpa [inner] using
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfInteriorSpatialPathInnerPairMeasurableEquiv_measurePreserving
        M N)

  have hIdOuter :
      MeasurePreserving (MeasurableEquiv.refl Outer) μOuter μOuter := by
    simpa using (MeasurePreserving.id μOuter)

  have hRefine :
      MeasurePreserving refine
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure
          (M + 2) N)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
    simpa [refine, μOuter,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfBoundaryInteriorSpatialHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfInnerPairDeepInteriorSpatialHaarMeasure,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure] using
      hIdOuter.prod hInner

  have hAll := hOuter.trans hRefine
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv,
    outer, inner, refine, Outer] using hAll

end

end MathlibAnalytic
end MGAP4D
