import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfClosureFlatCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeReduction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfCoordinateTransferBridgeSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfCoordinateTransferBridgeSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfCoordinateTransferBridgeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfCoordinateTransferBridgeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfCoordinateTransferBridgeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfCoordinateTransferBridgeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfCoordinateTransferBridgeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Measurable currying for finite-product coordinate fields.  It is stated
explicitly here because the positive-half geometry arrives as a flat product
index, whereas the transfer construction is naturally a path of slice
configurations. -/
def measurableEquivCurryPi
    (I J Value : Type*) [MeasurableSpace Value] :
    ((I × J) → Value) ≃ᵐ (I → J → Value) where
  toFun f i j := f (i, j)
  invFun f z := f z.1 z.2
  left_inv f := by
    funext z
    rfl
  right_inv f := by
    funext i j
    rfl
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply (i, j)
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro z
    exact (measurable_pi_apply z.2).comp (measurable_pi_apply z.1)

/-- Curry the flat `H+2` spatial-link layers from the actual positive closure
into the exact spatial-path carrier already used by the one-slab transfer
construction. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv
    (H N : ℕ) :
    PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N where
  toFun A j e := A (j, e)
  invFun path z := path z.1 z.2
  left_inv A := by
    funext z
    rfl
  right_inv path := by
    funext j e
    rfl
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro j
    rw [measurable_pi_iff]
    intro e
    exact measurable_pi_apply (j, e)
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro z
    exact (measurable_pi_apply z.2).comp (measurable_pi_apply z.1)

/-- Curry the flat `H+1` temporal-vertex layers into the exact temporal-link
field carrier used by the pathwise temporal-gauge reduction. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv
    (H N : ℕ) :
    PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N where
  toFun U i v := U (i, v)
  invFun U z := U z.1 z.2
  left_inv U := by
    funext z
    rfl
  right_inv U := by
    funext i v
    rfl
  measurable_toFun := by
    rw [measurable_pi_iff]
    intro i
    rw [measurable_pi_iff]
    intro v
    exact measurable_pi_apply (i, v)
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro z
    exact (measurable_pi_apply z.2).comp (measurable_pi_apply z.1)

/-- Combined flat-to-nested coordinate equivalence.  Its target is literally
the pair of carriers on which the #2057 temporal-gauge theorem is stated. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
    (H N : ℕ) :
    (PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :=
  MeasurableEquiv.prodCongr
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N)
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N)

/-- Haar law on the nested transfer-coordinate carrier, defined as the exact
pushforward of the already-proved flat positive-closure Haar law.  A later
Fubini unit can identify this with an iterated product of one-slice Haar laws;
no such identification is assumed here. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure
    (H N : ℕ) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :=
  Measure.map
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
      H N)
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure H N)

/-- Currying is measure preserving by construction of the nested Haar law. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinates_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
        H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureFlatHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
  refine ⟨
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
      H N).measurable, ?_⟩
  rfl

/-- The actual positive-closure boundary/open-half coordinates are measurably
equivalent directly to the path/temporal-field carriers used by temporal gauge
fixing. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
    (H N : ℕ) :
    PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :=
  (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)).trans
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv
      H N)

/-- Exact Haar transport from the actual selected positive closure to the
nested transfer-coordinate carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving
    (H N : ℕ) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
  exact
    (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv_measurePreserving_haar H N).trans
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinates_measurePreserving
        H N)

/-- In the actual positive-half coordinates, the chosen temporal gauge leaves
the primary spatial endpoint unchanged. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalGauge_primary
    (H N : ℕ)
    (A : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)
        ⟨0, Nat.zero_lt_succ _⟩ =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A
        ⟨0, Nat.zero_lt_succ _⟩ := by
  exact periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_zero
    H N
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)

/-- The antipodal endpoint retains exactly the terminal accumulated gauge
transformation in the actual positive-half coordinates.  It is deliberately
not simplified to a pointwise fixed endpoint. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalGauge_antipodal
    (H N : ℕ)
    (A : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
        H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTerminalGauge H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv
            H N U))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A
          (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) := by
  exact periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath_last
    H N
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)

/-- The #2057 pathwise temporal-gauge identity now applies directly to the
flat coordinates extracted from the actual positive closure. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatUnfixedPathKernel_eq_temporalGauge
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenPositiveHalfFlatSpatialPathConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (U : PeriodicHypercubicEvenPositiveHalfFlatTemporalFieldConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeSpatialPath
          H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge
      H N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv H N A)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv H N U)

end

end MathlibAnalytic
end MGAP4D