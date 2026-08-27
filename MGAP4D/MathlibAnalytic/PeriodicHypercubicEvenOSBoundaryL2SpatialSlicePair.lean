import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundarySpatialSlicePair
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osBoundaryL2SpatialSlicePairSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance osBoundaryL2SpatialSlicePairSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryL2SpatialSlicePairSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryL2SpatialSlicePairSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryL2SpatialSlicePairSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryL2SpatialSlicePairSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryL2SpatialSlicePairSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real Haar-`L²` on the full reflection-fixed Wilson boundary. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2
    (H N : ℕ) :=
  Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- Real Haar-`L²` on the ordered primary/antipodal pair of modern spatial
slices.  This is the same two-slice Haar carrier used by the transfer layer. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
    (H N : ℕ) :=
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The boundary-side and transfer-side names for one-slice Haar probability
are definitionally the same product measure. -/
theorem periodicHypercubicEvenBoundarySpatialSliceHaarMeasure_eq_specialUnitarySpatialSliceHaarMeasure
    (H N : ℕ) :
    periodicHypercubicEvenBoundarySpatialSliceHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  rfl

/-- Consequently the boundary-side ordered-pair Haar measure is exactly the
pair Haar measure already used by the one-slab transfer construction. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure_eq_specialUnitarySpatialSlicePairHaarMeasure
    (H N : ℕ) :
    periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure H N =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
  rfl

/-- The canonical boundary-to-two-slice measurable equivalence preserves the
actual transfer-side product Haar measure exactly. -/
theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ))
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  simpa only [
    periodicHypercubicEvenBoundarySpatialSlicePairHaarMeasure_eq_specialUnitarySpatialSlicePairHaarMeasure]
    using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_haar
        H N

/-- Pull a full boundary `L²` vector forward to the ordered pair of modern
spatial slices.  Mathlib's `Lp.compMeasurePreservingₗᵢ` makes this an exact
linear isometry; no representative-level point evaluation is used. -/
noncomputable def periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  exact MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ e.symm
    (MeasurePreserving.symm e h)

/-- Pull an ordered two-slice `L²` vector back to the original shared-boundary
carrier. -/
noncomputable def periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  exact MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ e h

/-- The forward `L²` isometry is literally composition with the inverse
boundary coordinate equivalence, almost everywhere for product Haar measure. -/
theorem periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      f ∘
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  change MeasureTheory.Lp.compMeasurePreserving e.symm
      (MeasurePreserving.symm e h) f =ᵐ[_] f ∘ e.symm
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (MeasurePreserving.symm e h)

/-- The reverse `L²` isometry is composition with the boundary coordinate
map itself, almost everywhere for the original boundary Haar measure. -/
theorem periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry_coeFn
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure H N]
      f ∘
        periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  change MeasureTheory.Lp.compMeasurePreserving e h f =ᵐ[_] f ∘ e
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f h

/-- Pulling boundary `L²` to the endpoint-pair carrier and back is exactly the
identity. -/
theorem periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N) :
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
        (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f) =
      f := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  let hs :
      MeasurePreserving e.symm
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
    MeasurePreserving.symm e h
  change MeasureTheory.Lp.compMeasurePreserving e h
      (MeasureTheory.Lp.compMeasurePreserving e.symm hs f) = f
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply f hs h]
  rw [Lp.ext_iff]
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f (hs.comp h)).trans
      (Filter.Eventually.of_forall fun x => by simp)

/-- Pulling an endpoint-pair `L²` vector back to the shared boundary and then
forward again is exactly the identity. -/
theorem periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f) =
      f := by
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let h :
      MeasurePreserving e
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
    simpa [e] using
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N
  let hs :
      MeasurePreserving e.symm
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
    MeasurePreserving.symm e h
  change MeasureTheory.Lp.compMeasurePreserving e.symm hs
      (MeasureTheory.Lp.compMeasurePreserving e h f) = f
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply f h hs]
  rw [Lp.ext_iff]
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f (h.comp hs)).trans
      (Filter.Eventually.of_forall fun x => by simp)

/-- Audit-visible package for the exact shared-boundary/two-endpoint `L²`
identification used before inserting the physical transfer operator. -/
structure PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePairPackage
    (H N : ℕ) : Prop where
  forwardNorm :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N,
      ‖periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f‖ = ‖f‖
  backwardNorm :
    ∀ f : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N,
      ‖periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N f‖ = ‖f‖
  leftInverse :
    Function.LeftInverse
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N)
      (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N)
  rightInverse :
    Function.RightInverse
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N)
      (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N)

/-- Construct the exact boundary/two-slice `L²` identification package. -/
theorem periodicHypercubicEvenOSBoundaryL2SpatialSlicePairPackage
    (H N : ℕ) :
    PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePairPackage H N :=
  { forwardNorm := fun f =>
      (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N).norm_map f
    backwardNorm := fun f =>
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N).norm_map f
    leftInverse :=
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse H N
    rightInverse :=
      periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse H N }

end

end MathlibAnalytic
end MGAP4D
