import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStrictPersistentResponse
import Mathlib.Tactic

/-!
# Persistent-response refined posterior influence

PR #5184 closes the fixed-volume first strict response bootstrap and produces a
boundary-independent persistent remote expectation-response radius

  epsilon_persist(H,beta)
    = ((width(beta)/2) * (width(beta)/(1-alpha_H(beta)))) / exp(-8 beta).

PR #5179 already provides the canonical map from any remote response matrix to
refined posterior influence data, with

* zero diagonal,
* the direct 32 beta local coefficient on plaquette-local pairs,
* the response-generated coefficient on remote pairs.

This file composes those two constructions.  It defines the persistent refined
influence profile and its finite row, column, and total coefficients, proves the
basic nonnegativity bounds needed for a second Dobrushin bootstrap, and records
that the entire persistent refined matrix vanishes at beta = 0.

No second strict cutoff is selected here.  In particular, no volume-uniform
strictness, Euclidean-time identification, continuum generator bridge, H1-D5
exact descent, or complete Yang--Mills mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorPersistentRefinedInfluenceSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Persistent-response refined influence: direct local coefficient on
plaquette-local pairs and the strict persistent response coefficient on remote
pairs. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
    H beta
    (fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
        H beta)
    target source

/-- The terminal-free strict persistent response radius vanishes exactly at
zero coupling. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_zero
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
        H 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth]

/-- The persistent refined influence is nonnegative throughout the first
fixed-volume strict cutoff. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H beta target source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
      H beta hbeta
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
          H beta)
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_nonneg
          H beta hbeta hbetaPos hbetaCutoff)
      target source

/-- The persistent refined influence still has zero diagonal. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_diagonal
    (H : ℕ)
    (beta : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H beta target target = 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_diagonal
      H beta
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
          H beta)
      target

/-- Every persistent refined entry vanishes at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_zero
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H 0 target source = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp [hlocal]
    · simp [
        hlocal,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence]

/-- Concrete posterior non-strict influence data obtained by applying the
refinement map of PR #5179 to the persistent response matrix of PR #5184. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B :=
  (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRemoteExpectationResponseMatrixData
    H N hN beta hbeta hbetaPos hbetaCutoff).toRefinedInfluenceData B

/-- The concrete persistent refined data carry exactly the scalar persistent
refined influence profile above. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData_influence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
      H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H beta target source := by
  rfl

/-- Row sum of the persistent refined influence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum
    (H : ℕ)
    (beta : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
      H beta target source

/-- Column sum of the persistent refined influence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
      H beta target source

/-- Total finite persistent refined influence mass.  This is the natural scalar
candidate for the second fixed-volume Dobrushin bootstrap. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
    (H : ℕ)
    (beta : ℝ) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
        H beta target source

/-- The persistent total coefficient is nonnegative inside the first strict
cutoff. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
  apply Finset.sum_nonneg
  intro target _hTarget
  apply Finset.sum_nonneg
  intro source _hSource
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_nonneg
      H beta hbeta hbetaPos hbetaCutoff target source

/-- Every persistent refined row is bounded by the total persistent coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum_le_totalCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum
        H beta target ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
  apply
    Finset.single_le_sum
      (fun t _ =>
        Finset.sum_nonneg fun s _ =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_nonneg
            H beta hbeta hbetaPos hbetaCutoff t s)
      (Finset.mem_univ target)

/-- Every persistent refined column is bounded by the same total coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum_le_totalCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum
        H beta source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
  rw [Finset.sum_comm]
  apply
    Finset.single_le_sum
      (fun s _ =>
        Finset.sum_nonneg fun t _ =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_nonneg
            H beta hbeta hbetaPos hbetaCutoff t s)
      (Finset.mem_univ source)

/-- The concrete persistent refined data inherit the row total bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData_rowSum_le_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedRowSum_le_totalCoefficient
      H beta hbeta hbetaPos hbetaCutoff target

/-- The concrete persistent refined data inherit the column total bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData_columnSum_le_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedColumnSum_le_totalCoefficient
      H beta hbeta hbetaPos hbetaCutoff source

/-- The persistent total coefficient vanishes at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_zero
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H 0 = 0 := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient]

end

end MathlibAnalytic
end MGAP4D
