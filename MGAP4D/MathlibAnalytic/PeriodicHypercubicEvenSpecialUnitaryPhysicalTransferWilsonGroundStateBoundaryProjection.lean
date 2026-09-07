import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwoBoundaryGeometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The Hilbert adjoint of the left-boundary pullback.  It is the abstract
conditional expectation back to the left vacuum boundary carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) →L[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta).toContinuousLinearMap†

/-- The left-boundary adjoint is a left inverse to the isometric left-boundary
pullback. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint_comp_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
          H N hN beta hbeta u) = u := by
  let J := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta
  let L := J.toContinuousLinearMap
  change L† (L u) = u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact LinearIsometry.inner_map_map J u v

/-- Orthogonal projection in joint `L²` onto the closed left-boundary
subspace.  This is the coarse Wilson conditional expectation geometry, defined
without a pointwise kernel-output formula. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) →L[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
  let J := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta
  J.toContinuousLinearMap.comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint
      H N hN beta hbeta)

/-- The coarse boundary conditional expectation is idempotent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
      H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro y
  let J := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint
    H N hN beta hbeta
  change J (A (J (A y))) = J (A y)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint_comp_left]

/-- The coarse boundary conditional expectation is self-adjoint/symmetric. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_inner_symm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
      H N hN beta hbeta :
      Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) →L[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)) :
      Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta) →ₗ[ℝ]
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)).IsSymmetric := by
  intro x y
  let J := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta
  let L := J.toContinuousLinearMap
  change inner ℝ (L (L† x)) y = inner ℝ x (L (L† y))
  calc
    inner ℝ (L (L† x)) y = inner ℝ (L† x) (L† y) := by
      symm
      exact ContinuousLinearMap.adjoint_inner_right L (L† x) y
    _ = inner ℝ x (L (L† y)) :=
      ContinuousLinearMap.adjoint_inner_left L (L† y) x

/-- The Doob boundary operator is the right-boundary pullback followed by
conditional expectation to the left boundary. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) →L[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryAdjoint
    H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta).toContinuousLinearMap

/-- Coarse projection of a right-boundary vector is exactly the left-boundary
pullback of its Doob conditional expectation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
          H N hN beta hbeta u) := by
  rfl

/-- The norm of the coarse projection of a right-boundary vector is the norm
of its Doob boundary conditional expectation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta u)‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
        H N hN beta hbeta u‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary]
  exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
    H N hN beta hbeta).norm_map _

end

end MathlibAnalytic
end MGAP4D