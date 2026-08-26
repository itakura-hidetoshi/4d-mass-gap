import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicHypercubicEvenOSBoundaryPairL2SpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The real Haar-`L²` space on the genuine shared OS reflection boundary. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- The real Haar-`L²` space on the ordered pair of modern spatial slices.  Its
measure is exactly the product of the two one-slab spatial-slice Haar laws. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryOneSlabSpatialSlicePairL2
    (H N : ℕ) : Type :=
  Lp ℝ 2
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The boundary-side name for one spatial-slice Haar probability is literally
the same product Haar law used by the modern one-slab transfer. -/
theorem periodicHypercubicEvenBoundarySpatialSliceHaarMeasure_eq_oneSlabHaarMeasure
    (H N : ℕ) :
    periodicHypercubicEvenBoundarySpatialSliceHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  rfl

/-- After the already-proved two-slice coordinate equivalence, the genuine OS
boundary Haar probability is carried exactly to the product of the two modern
one-slab spatial-slice Haar probabilities. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  simpa [periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure,
    periodicHypercubicEvenBoundarySpatialSliceHaarMeasure,
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
      H N

/-- Pull an OS-boundary square-integrable function forward to the two modern
spatial-slice coordinates.  The map is an exact real linear isometry because
the inverse coordinate map is measure preserving. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOSBoundaryToSpatialSlicePairLinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryOneSlabSpatialSlicePairL2 H N := by
  let E := periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let hE :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
      H N
  exact MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ E.symm
    (MeasurePreserving.symm E hE)

/-- The boundary-to-two-slice `L²` isometry is onto.  An explicit preimage is
obtained by pullback along the forward boundary coordinate equivalence. -/
theorem periodicHypercubicEvenSpecialUnitaryOSBoundaryToSpatialSlicePairLinearIsometry_surjective
    (H N : ℕ) :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryOSBoundaryToSpatialSlicePairLinearIsometry
        H N) := by
  intro g
  let E := periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let hE :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
      H N
  let hEsymm := MeasurePreserving.symm E hE
  let f : PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2 H N :=
    MeasureTheory.Lp.compMeasurePreserving E hE g
  refine ⟨f, ?_⟩
  change MeasureTheory.Lp.compMeasurePreserving E.symm hEsymm
      (MeasureTheory.Lp.compMeasurePreserving E hE g) = g
  have hcomp :=
    MeasureTheory.Lp.compMeasurePreserving_comp_apply
      (E := ℝ) (p := (2 : ℝ≥0∞)) g hE hEsymm
  simpa [E] using hcomp.symm

/-- Canonical Hilbert-space identification between the actual OS shared-boundary
`L²` carrier and the product-coordinate `L²` carrier built from two copies of
the modern one-slab spatial slice. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2 H N ≃ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryOneSlabSpatialSlicePairL2 H N :=
  LinearIsometryEquiv.ofSurjective
    (periodicHypercubicEvenSpecialUnitaryOSBoundaryToSpatialSlicePairLinearIsometry H N)
    (periodicHypercubicEvenSpecialUnitaryOSBoundaryToSpatialSlicePairLinearIsometry_surjective
      H N)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair_norm
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2 H N) :
    ‖periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair H N f‖ =
      ‖f‖ :=
  (periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair H N).norm_map f

/-- Audit-visible `L²` carrier bridge from the genuine finite OS reflection
boundary to two copies of the modern one-slab spatial-slice configuration. -/
structure PeriodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package
    (H N : ℕ) : Prop where
  boundaryMeasureTransport :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  l2NormTransport :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2 H N,
      ‖periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair H N f‖ =
        ‖f‖

/-- Construct the exact OS-boundary/two-slice Haar-`L²` bridge package. -/
theorem periodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package H N :=
  { boundaryMeasureTransport :=
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
        H N
    l2NormTransport :=
      periodicHypercubicEvenSpecialUnitaryOSBoundaryHaarL2EquivSpatialSlicePair_norm
        H N }

end

end MathlibAnalytic
end MGAP4D
