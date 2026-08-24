import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointPhysicalTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenvector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

local instance positiveHalfClosureEndpointOperatorSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointOperatorSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance positiveHalfClosureEndpointOperatorSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfClosureEndpointOperatorSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfClosureEndpointOperatorSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfClosureEndpointOperatorSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfClosureEndpointOperatorSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical constant unit Gauss-law state witnesses that the actual
one-slice physical Hilbert space is nontrivial.  This is derived from the
existing concrete norm-one state, rather than imposed as a new assumption. -/
local instance positiveHalfClosureEndpointOperatorPhysicalNontrivial (H N : ℕ) :
    Nontrivial
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hu : u ≠ 0 := by
    intro hzero
    have hnormu : ‖u‖ = 1 := by
      simpa [u] using
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
    rw [hzero, norm_zero] at hnormu
    norm_num at hnormu
  exact ⟨⟨u, 0, hu⟩⟩

/-- The finite-volume positive-half OS closure endpoint form is represented on
actual Gauss-law one-slice Hilbert space by the partition square-root
normalization times the already constructed positive-half physical transfer
power.  This definition upgrades the scalar identity of the preceding bridge
to an actual bounded operator carrier. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta •
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN beta hbeta

@[simp] theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_apply
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta f =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f := by
  rfl

/-- The partition square-root normalization appearing in the endpoint operator
is nonnegative. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤ periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta := by
  unfold periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
  exact Real.sqrt_nonneg _

/-- Exact Riesz pairing identity for the actual positive-half closure endpoint
operator.  Its matrix coefficient is literally the completed positive OS Gram
feature integrated against the two Gauss-law endpoint states on the actual
positive-closure Haar law. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta f) g =
      ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          (f : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
          (g : Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1
              (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) := by
  simpa [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator,
    inner_smul_left] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_gaussEndpoint_integral_eq_normalizedPhysicalTransfer
      H N hN beta hbeta f g).symm

/-- The endpoint operator has the exact norm obtained by scalar multiplication
of the existing physical positive-half transfer power.  The concrete norm-one
Gauss-law state above supplies the nontrivial carrier needed for the exact
operator-norm scalar law. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_norm
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta‖ := by
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg
      (periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization_nonneg
        H N hN beta hbeta)]

/-- Consequently every represented endpoint vector satisfies the sharp generic
operator-norm estimate inherited from the physical transfer carrier. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_norm_apply_le
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta f‖ ≤
      (periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta‖) * ‖f‖ := by
  have h := ContinuousLinearMap.le_opNorm
    (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
      H N hN beta hbeta) f
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_norm
    H N hN beta hbeta] at h
  exact h

/-- Riesz uniqueness: the #2066 closure endpoint matrix coefficients determine
the bounded Gauss-law operator uniquely.  Thus the endpoint operator above is
not merely a convenient definition of `c • T`; it is the unique bounded
operator representing the actual closure integral for every pair of physical
one-slice states. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_unique
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hA : ∀ f g :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ (A f) g =
        ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) :
    A = periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
      H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  rw [hA f g]
  symm
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_inner_eq_integral
      H N hN beta hbeta f g

/-- Audit-visible package for the finite-volume endpoint-operator upgrade. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperatorPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  normalizationNonneg :
    0 ≤ periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
      H N hN beta hbeta
  operatorNorm :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta‖
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
            H N hN beta hbeta f) g =
        ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            (f : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
            (g : Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1
                (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)
  uniqueRepresentation :
    ∀ A :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      (∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
        inner ℝ (A f) g =
          ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
              (Matrix.specialUnitaryGroup (Fin N) ℂ),
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta z.1 z.2 *
              (f : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                  H N z).1 0) *
              (g : Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
                ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                  H N z).1
                  (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
            ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) →
        A = periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
          H N hN beta hbeta

/-- Construct the complete endpoint-operator representation package. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperatorPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperatorPackage
      H N hN beta hbeta :=
  { normalizationNonneg :=
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization_nonneg
        H N hN beta hbeta
    operatorNorm :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_norm
        H N hN beta hbeta
    pairing :=
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_inner_eq_integral
        H N hN beta hbeta
    uniqueRepresentation := fun A hA =>
      periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator_unique
        H N hN beta hbeta A hA }

end

end MathlibAnalytic
end MGAP4D