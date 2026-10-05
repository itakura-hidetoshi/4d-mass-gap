import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanBlockMinorization
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Tactic

/-!
# Posterior random-scan Doeblin residual

The finite posterior full-block minorization of PR #5173 gives

  delta * nu <= K(A, ·),

where delta = (n⁻¹ * exp(-16 beta))^n and nu is the common full Haar-refresh
law.  This file removes that common component, proves the residual row has
exact mass rho = 1 - delta, and records rho < 1 at every fixed finite volume.

No volume-uniform lower bound is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance posteriorRandomScanDoeblinResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorRandomScanDoeblinResidualTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanDoeblinResidualCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanDoeblinResidualSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanDoeblinResidualMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanDoeblinResidualBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorRandomScanDoeblinResidualFullHaarProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
  exact
    (inferInstance :
      IsMarkovKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H))).isProbabilityMeasure (fun _ => 1)

/-- The uniform posterior one-link selection coefficient is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient_pos
    (H : ℕ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
        H := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient
  exact ENNReal.inv_pos.2 (by simp)

/-- The posterior one-link Haar coefficient exp(-16 beta) is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient_pos
    (beta : ℝ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- The finite-volume posterior full-block Doeblin coefficient is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient_pos
    (H : ℕ)
    (beta : ℝ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
  exact
    ENNReal.pow_pos
      (ENNReal.mul_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanCoefficient_pos
          H).ne'
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorOneLinkHaarMinorizationCoefficient_pos
          beta).ne')
      _

/-- The posterior full-block coefficient is at most one because its common
Haar component is dominated by an actual probability row. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta ≤ 1 := by
  let delta : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu : Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  have hMinor : delta • nu ≤ K A := by
    dsimp [delta, nu, K]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlock_lower_bound_commonHaarRefresh
        H N hN beta hbeta B A
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  letI : IsProbabilityMeasure (K A) :=
    (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
  have hUniv := Measure.le_iff.1 hMinor Set.univ MeasurableSet.univ
  simpa [delta, Measure.smul_apply, measure_univ] using hUniv

/-- Positive residual row after removing the common full-Haar Doeblin
component from one posterior full block. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length A -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N

/-- Every posterior residual row is finite. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_isFiniteMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
        H N hN beta hbeta B A) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  letI : IsProbabilityMeasure (K A) :=
    (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
  infer_instance

/-- Exact decomposition into posterior residual plus the common Haar component. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_add_commonHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
        H N hN beta hbeta B A +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
          H beta •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
          H N =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  let common :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
        H beta •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  have hMinor : common ≤ K A := by
    dsimp [common, K]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlock_lower_bound_commonHaarRefresh
        H N hN beta hbeta B A
  letI : IsProbabilityMeasure (K A) :=
    (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
  letI : IsFiniteMeasure common :=
    isFiniteMeasure_of_le (K A) hMinor
  simpa [
    common,
    K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
  ] using (Measure.sub_add_cancel_of_le hMinor)

/-- The posterior residual row has exact total mass 1 - delta. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
        H N hN beta hbeta B A Set.univ =
      1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
          H beta := by
  let delta : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu : Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  have hMinor : common ≤ K A := by
    dsimp [common, delta, nu, K]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlock_lower_bound_commonHaarRefresh
        H N hN beta hbeta B A
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  letI : IsProbabilityMeasure (K A) :=
    (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
  letI : IsFiniteMeasure common :=
    isFiniteMeasure_of_le (K A) hMinor
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
  rw [Measure.sub_apply MeasurableSet.univ hMinor]
  simp [K, common, delta, nu, Measure.smul_apply, measure_univ]

/-- Named posterior full-block residual mass rho = 1 - delta. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
    (H : ℕ)
    (beta : ℝ) : ℝ≥0∞ :=
  1 -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta

/-- Every residual row has the named residual mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
        H N hN beta hbeta B A Set.univ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
  ] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ
      H N hN beta hbeta B A

/-- The named posterior residual mass is finite. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_ne_top
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta ≠ ∞ := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass]

/-- The named posterior residual mass is strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_lt_one
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta < 1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
  exact
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient_pos
        H beta).ne'

end

end MathlibAnalytic
end MGAP4D
