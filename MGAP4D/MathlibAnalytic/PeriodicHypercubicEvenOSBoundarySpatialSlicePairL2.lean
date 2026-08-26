import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalCompletedBoundarySpatialSlicePairL2
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

/-- The already-canonical boundary-to-two-slice Haar-`L²` isometry is onto.

The preimage of a two-slice class is its measure-preserving pullback along the
forward boundary-coordinate equivalence.  Thus the completed shared-boundary
`L²` carrier and the product-Haar `L²` carrier containing the actual one-slab
Wilson kernel are not merely isometric subspaces: they are canonically
isometrically equivalent. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_surjective
    (H N : ℕ) :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2 H N) := by
  intro g
  let E := periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
    (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let hE :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
      H N
  let hEsymm :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_measurePreserving_oneSlabHaar
      H N
  let f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
    MeasureTheory.Lp.compMeasurePreserving E hE g
  refine ⟨f, ?_⟩
  change MeasureTheory.Lp.compMeasurePreserving E.symm hEsymm
      (MeasureTheory.Lp.compMeasurePreserving E hE g) = g
  have hcomp :=
    MeasureTheory.Lp.compMeasurePreserving_comp_apply
      (E := ℝ) (p := (2 : ℝ≥0∞)) g hE hEsymm
  simpa [E] using hcomp.symm

/-- Canonical Hilbert-space identification between the genuine finite OS
shared-boundary `L²` carrier and the product-coordinate `L²` carrier on two
modern spatial slices. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N ≃ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2 H N :=
  LinearIsometryEquiv.ofSurjective
    (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2 H N)
    (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_surjective H N)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2_norm
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    ‖periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2 H N f‖ =
      ‖f‖ :=
  (periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2 H N).norm_map f

/-- Audit-visible package for the exact shared-boundary/product-pair Haar-`L²`
identification.  The measure transport and the isometric embedding are the
canonical carriers already used by the actual Wilson OS realization; the new
content is surjectivity, hence a genuine Hilbert-space equivalence. -/
structure PeriodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package
    (H N : ℕ) : Prop where
  boundaryMeasureTransport :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
  l2Surjective :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2 H N)
  l2NormTransport :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N,
      ‖periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2 H N f‖ =
        ‖f‖

/-- Construct the exact OS-boundary/two-slice Haar-`L²` equivalence package
without introducing any new physical assumption or transfer-operator claim. -/
theorem periodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryOSBoundarySpatialSlicePairL2Package H N :=
  { boundaryMeasureTransport :=
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_oneSlabHaar
        H N
    l2Surjective :=
      periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_surjective H N
    l2NormTransport :=
      periodicHypercubicEvenSpecialUnitaryBoundaryL2EquivSpatialSlicePairL2_norm H N }

end

end MathlibAnalytic
end MGAP4D
