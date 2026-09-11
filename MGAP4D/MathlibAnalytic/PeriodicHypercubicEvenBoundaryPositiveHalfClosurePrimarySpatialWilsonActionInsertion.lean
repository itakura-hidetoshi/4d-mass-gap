import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableInsertion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance primarySpatialWilsonInsertionSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _

local instance primarySpatialWilsonInsertionSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance primarySpatialWilsonInsertionSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primarySpatialWilsonInsertionSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primarySpatialWilsonInsertionSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primarySpatialWilsonInsertionSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primarySpatialWilsonInsertionSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The intrinsic spatial Wilson action, regarded as an actual bounded
continuous observable on the compact one-slice configuration space. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N :=
  BoundedContinuousFunction.mkOfCompact
    ⟨periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H N⟩

@[simp] theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_apply
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N A =
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A :=
  rfl

/-- The bounded observable realization retains the already-proved exact
lattice gauge invariance of the spatial Wilson action. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N) := by
  intro γ A
  exact periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant H N γ A

/-- Multiplication by the actual spatial Wilson action on the physical
Gauss-law one-slice Hilbert carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalSpatialWilsonActionMulOperator
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
    H N
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
      H N)

/-- The positive-half endpoint operator with the actual spatial Wilson action
inserted at the primary fixed slice. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
      H N)

/-- Exact finite Wilson generator bridge: the matrix coefficient of the
primary spatial-Wilson-action insertion operator is literally the actual
positive-half closure Haar integral with `S_spatial(A₀)` inserted. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℝ
        (periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator
          H N hN beta hbeta f) g =
      ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin N) ℂ),
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2 *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
              H N z).1 0) *
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
  simpa [periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator]
    using
      (periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_inner_eq_integral
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
          H N) f g)

/-- The concrete Wilson-action insertion inherits the generic bounded
multiplication estimate. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ *
        ‖periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N‖ := by
  exact
    periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableOperator_norm_le
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable_gaugeInvariant
        H N)

/-- Audit-visible package for the first actual Wilson action generator inserted
on the positive-half endpoint carrier. -/
structure PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  pairing :
    ∀ f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N,
      inner ℝ
          (periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator
            H N hN beta hbeta f) g =
        ∫ z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
            (Matrix.specialUnitaryGroup (Fin N) ℂ),
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta z.1 z.2 *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
                H N z).1 0) *
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
  normLe :
    ‖periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryPositiveHalfClosureEndpointOperator
        H N hN beta hbeta‖ *
        ‖periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H N‖

/-- Construct the complete primary spatial-Wilson-action insertion package. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionPackage
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionPackage
      H N hN beta hbeta :=
  { pairing :=
      periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator_inner_eq_integral
        H N hN beta hbeta
    normLe :=
      periodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionOperator_norm_le
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D