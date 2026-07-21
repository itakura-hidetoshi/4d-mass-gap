import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanVacuumSectorL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A finite noncommutative product preserves a fixed left inner-product
coefficient whenever every factor preserves that coefficient. -/
theorem continuousLinearMap_inner_left_noncommProd_eq_of_each
    {ι : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (u : Finset ι)
    (A : ι → V →L[ℝ] V)
    (hComm : (u : Set ι).Pairwise (Commute on A))
    (omega : V)
    (hPreserve : ∀ i ∈ u, ∀ f : V,
      inner ℝ omega (A i f) = inner ℝ omega f)
    (f : V) :
    inner ℝ omega (u.noncommProd A hComm f) = inner ℝ omega f := by
  have hAll :
      ∀ g : V,
        inner ℝ omega (u.noncommProd A hComm g) = inner ℝ omega g :=
    Finset.noncommProd_induction
      u A hComm
      (fun T : V →L[ℝ] V =>
        ∀ g : V, inner ℝ omega (T g) = inner ℝ omega g)
      (fun X Y hX hY g => by
        change inner ℝ omega (X (Y g)) = inner ℝ omega g
        rw [hX (Y g), hY g])
      (by intro g; rfl)
      (fun i hi => hPreserve i hi)
  exact hAll f

/-- The empty-label canonical fluctuation-sector projector preserves the Gibbs
vacuum coefficient.  Its factors are precisely the one-link heat-bath
projections. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationJointSectorProjectorL2_empty
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2
          ∅ f) =
      inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f := by
  classical
  let C := periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
  let Q : C.base.geometry.Edge →
      Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
    fun edge => C.singleLinkHeatBathFluctuationL2 edge
  have hQComm : ∀ target source : C.base.geometry.Edge,
      ∀ g : Lp ℝ 2 C.gibbsMeasure,
        Q target (Q source g) = Q source (Q target g) := by
    intro target source g
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkHeatBathFluctuationL2_pairwise_comm_for_commuting_family
        target source g
  have hPreserve :
      ∀ edge ∈ (Finset.univ : Finset C.base.geometry.Edge),
        ∀ g : Lp ℝ 2 C.gibbsMeasure,
          inner ℝ C.gibbsVacuumL2
              (continuousLinearMapJointSectorFactorL2 Q ∅ edge g) =
            inner ℝ C.gibbsVacuumL2 g := by
    intro edge _hedge g
    have hProjection :
        inner ℝ C.gibbsVacuumL2
            (C.singleLinkHeatBathProjectionL2 edge g) =
          inner ℝ C.gibbsVacuumL2 g := by
      calc
        inner ℝ C.gibbsVacuumL2
            (C.singleLinkHeatBathProjectionL2 edge g) =
          inner ℝ
              (C.singleLinkHeatBathProjectionL2 edge C.gibbsVacuumL2) g := by
            symm
            exact
              continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
                C edge C.gibbsVacuumL2 g
        _ = inner ℝ C.gibbsVacuumL2 g := by
          rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum]
    simpa [Q, continuousLinearMapJointSectorFactorL2,
      continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
      hProjection
  have hGeneric :=
    continuousLinearMap_inner_left_noncommProd_eq_of_each
      (u := Finset.univ)
      (A := continuousLinearMapJointSectorFactorL2 Q ∅)
      (hComm := continuousLinearMapJointSectorFactorL2_pairwise_comm Q ∅ hQComm)
      C.gibbsVacuumL2 hPreserve f
  simpa [C, Q,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationJointSectorProjectorL2]
    using hGeneric

/-- The cardinality-zero fluctuation projector preserves the normalized Gibbs
vacuum coefficient. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationCardinalityProjectorL2_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) =
      inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f := by
  classical
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
    continuousLinearMapCardinalitySectorProjectorL2
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationJointSectorProjectorL2_empty
      f

/-- On every input, the cardinality-zero spectral projector is exactly the
orthogonal rank-one projection onto the normalized Gibbs-vacuum line. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  have hRange :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f ∈
        LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0).toLinearMap := by
    exact ⟨f, rfl⟩
  have hVacuumLine :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f ∈
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumLineL2 := by
    rw [←
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_zero_eq_vacuumLineL2]
    exact hRange
  have hLine :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumLineL2_iff
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f)).mp hVacuumLine
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f) •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 :=
      hLine
    _ = inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationCardinalityProjectorL2_zero]

/-- The cardinality-zero projector annihilates exactly the Gibbs-vacuum
orthogonal vectors. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_iff_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f = 0 ↔
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 := by
  constructor
  · intro hZero
    have hCoefficient :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationCardinalityProjectorL2_zero
        f
    simpa [hZero] using hCoefficient.symm
  · intro hOrthogonal
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hOrthogonal, zero_smul]

/-- Pointwise vacuum-orthogonal annihilation form of the cardinality-zero
projector theorem. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f = 0 := by
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_iff_inner_vacuum_eq_zero
      f).2 hOrthogonal

/-- Compact receipt for the exact cardinality-zero vacuum projection formula
and its vacuum-orthogonal kernel characterization. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorFormulaL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f) =
      inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
        f) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f = 0 ↔
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0)

/-- The exact beta-zero random-scan vacuum-projector formula receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorFormulaL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanVacuumProjectorFormulaL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_fluctuationCardinalityProjectorL2_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_zero_iff_inner_vacuum_eq_zero⟩

end

end MathlibAnalytic
end MGAP4D
