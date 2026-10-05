import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorPersistentRefinedInfluence
import Mathlib.Tactic

/-!
# Persistent-response second fixed-volume Dobrushin bootstrap

PR #5185 defines the boundary-independent persistent refined influence matrix
obtained by feeding the strict geometric response of PR #5184 back through the
refinement map of PR #5179.

This file proves that the resulting total coefficient is continuous at the
exactly decoupled point beta = 0 and vanishes there.  Consequently every fixed
finite side H admits a second positive coupling cutoff, chosen strictly inside
the first cutoff of PR #5180, on which the persistent refined matrix is itself
strict Dobrushin.

Thus the response -> refined influence -> strictness loop closes once at fixed
finite volume.

The cutoff remains H-dependent.  No volume-uniform strictness, Euclidean-time
identification, continuum generator bridge, H1-D5 exact descent, or complete
Yang--Mills mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorPersistentStrictDobrushinSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The terminal-free strict persistent response radius is continuous at the
exactly decoupled point. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_zero
    (H : ℕ) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
          H beta)
      0 := by
  let width : ℝ → ℝ := fun beta =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let alpha : ℝ → ℝ := fun beta =>
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  have hWidth : Continuous width := by
    dsimp [width]
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
    fun_prop
  have hAlpha : Continuous alpha := by
    dsimp [alpha]
    exact
      continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H
  have hOneSubAlpha :
      ContinuousAt (fun beta : ℝ => 1 - alpha beta) 0 :=
    continuousAt_const.sub hAlpha.continuousAt
  have hOneSubAlphaNe : 1 - alpha 0 ≠ 0 := by
    simp [alpha]
  have hHalf :
      ContinuousAt (fun beta : ℝ => width beta / 2) 0 :=
    hWidth.continuousAt.div continuousAt_const (by norm_num)
  have hRatio :
      ContinuousAt (fun beta : ℝ => width beta / (1 - alpha beta)) 0 :=
    hWidth.continuousAt.div hOneSubAlpha hOneSubAlphaNe
  have hNumerator :
      ContinuousAt
        (fun beta : ℝ =>
          (width beta / 2) * (width beta / (1 - alpha beta)))
        0 :=
    hHalf.mul hRatio
  have hExp :
      ContinuousAt (fun beta : ℝ => Real.exp (-8 * beta)) 0 := by
    fun_prop
  have hExpNe : Real.exp (-8 * (0 : ℝ)) ≠ 0 :=
    Real.exp_ne_zero _
  have hRadius :=
    hNumerator.div hExp hExpNe
  simpa [
    width,
    alpha,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
  ] using hRadius

/-- The response-generated remote coefficient based on the persistent response
radius is continuous at beta = 0. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_firstBootstrapStrictPersistent_zero
    (H : ℕ) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
          beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
            H beta))
      0 := by
  let eps : ℝ → ℝ := fun beta =>
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius
      H beta
  let floor : ℝ → ℝ := fun beta => Real.exp (-8 * beta)
  have hEps : ContinuousAt eps 0 := by
    dsimp [eps]
    exact
      continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentResponseRadius_zero
        H
  have hFloor : Continuous floor := by
    dsimp [floor]
    fun_prop
  have hFloorNe : floor 0 ≠ 0 := by
    dsimp [floor]
    exact Real.exp_ne_zero _
  have hRatio :
      ContinuousAt (fun beta : ℝ => eps beta / floor beta) 0 :=
    hEps.div hFloor.continuousAt hFloorNe
  let R : ℝ → ℝ := fun beta => 2 * (eps beta / floor beta)
  have hR : ContinuousAt R 0 := by
    dsimp [R]
    exact continuousAt_const.mul hRatio
  let E : ℝ → ℝ := fun beta => Real.exp (R beta)
  have hE : ContinuousAt E 0 := by
    dsimp [E]
    exact Real.continuous_exp.continuousAt.comp hR
  have hDenNe : E 0 + 1 ≠ 0 := by
    dsimp [E]
    positivity
  have hInfluence :
      ContinuousAt
        (fun beta : ℝ => (E beta - 1) / (E beta + 1))
        0 :=
    (hE.sub continuousAt_const).div
      (hE.add continuousAt_const) hDenNe
  simpa [
    eps,
    floor,
    R,
    E,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
  ] using hInfluence

/-- Every fixed persistent refined influence entry is continuous at beta = 0. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_zero
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
          H beta target source)
      0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simpa [hdiag] using
      (continuousAt_const :
        ContinuousAt (fun _beta : ℝ => (0 : ℝ)) 0)
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp only [hlocal, if_true]
      exact
        continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence.continuousAt
    · simp only [hlocal, if_false]
      exact
        continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_firstBootstrapStrictPersistent_zero
          H

/-- The finite total persistent refined coefficient is continuous at beta = 0. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_zero
    (H : ℕ) :
    ContinuousAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
          H beta)
      0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
  apply tendsto_finset_sum (Finset.univ :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  intro target _hTarget
  apply tendsto_finset_sum (Finset.univ :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  intro source _hSource
  exact
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluence_zero
      H target source

/-- A scalar family continuous at zero and equal to zero there is strictly
below one on a positive right neighborhood. -/
private theorem continuousAt_zero_exists_positive_lt_one
    (f : ℝ → ℝ)
    (hf : ContinuousAt f 0)
    (h0 : f 0 = 0) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      ∀ beta : ℝ, 0 < beta → beta < cutoff → f beta < 1 := by
  rw [Metric.continuousAt_iff] at hf
  obtain ⟨delta, hDelta, hControl⟩ :=
    hf 1 (by norm_num)
  refine ⟨delta / 2, by positivity, ?_⟩
  intro beta hbeta hbetaCutoff
  have hDist : dist beta 0 < delta := by
    rw [Real.dist_eq]
    simp [abs_of_pos hbeta]
    linarith
  have hImage := hControl hDist
  rw [h0] at hImage
  have hAbs : |f beta| < 1 := by
    simpa [Real.dist_eq] using hImage
  exact lt_of_le_of_lt (le_abs_self (f beta)) hAbs

/-- Every fixed finite side admits a second positive Dobrushin cutoff for the
persistent refined matrix, chosen strictly inside the first-bootstrap cutoff. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
    (H : ℕ) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      cutoff <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H ∧
      ∀ beta : ℝ, 0 < beta → beta < cutoff →
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
            H beta < 1 := by
  obtain ⟨localCutoff, hLocalPos, hLocal⟩ :=
    continuousAt_zero_exists_positive_lt_one
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
          H beta)
      (continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_zero
        H)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_zero
        H)
  let firstCutoff :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
      H
  have hFirstPos : 0 < firstCutoff := by
    dsimp [firstCutoff]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_pos
        H
  let cutoff := min localCutoff (firstCutoff / 2)
  refine ⟨cutoff, ?_, ?_, ?_⟩
  · dsimp [cutoff]
    exact lt_min hLocalPos (by positivity)
  · dsimp [cutoff]
    calc
      min localCutoff (firstCutoff / 2) ≤ firstCutoff / 2 :=
        min_le_right _ _
      _ < firstCutoff := by linarith
  · intro beta hbeta hbetaCutoff
    apply hLocal beta hbeta
    exact
      lt_of_lt_of_le hbetaCutoff
        (by
          dsimp [cutoff]
          exact min_le_left _ _)

/-- Canonically selected second fixed-volume cutoff for the persistent refined
matrix. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
    (H : ℕ) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
      H)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_pos
    (H : ℕ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
        H :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
      H)).1

/-- The second cutoff lies strictly inside the first-bootstrap strict interval,
so all persistent-response constructions used to define it are valid. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_lt_firstBootstrapCutoff
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
        H <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
        H :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
      H)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
    (H : ℕ)
    (beta : ℝ)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
      H)).2.2
    beta hbetaPos hbetaCutoff

/-- Inside the second cutoff, the persistent refined influence data themselves
form strict posterior Dobrushin matrix data. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
      H N hN beta hbeta B := by
  have hFirstCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H :=
    lt_trans hbetaCutoff
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_lt_firstBootstrapCutoff
        H)
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
      H N hN beta hbeta hbetaPos hFirstCutoff B
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
      H beta
  refine
    { toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData := D
      coefficient := coefficient
      coefficient_nonneg := ?_
      rowSum_le_coefficient := ?_
      coefficient_lt_one := ?_ }
  · dsimp [coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient_nonneg
        H beta hbeta hbetaPos hFirstCutoff
  · intro target
    dsimp [D, coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData_rowSum_le_totalCoefficient
        H N hN beta hbeta hbetaPos hFirstCutoff B target
  · dsimp [coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
        H beta hbetaPos hbetaCutoff

/-- Every row of the persistent-refined second-bootstrap matrix is strictly
below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData_rowSum_lt_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) < 1 := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  exact lt_of_le_of_lt (D.rowSum_le_coefficient target) D.coefficient_lt_one

/-- The same persistent total coefficient controls every column, preparing the
strict random-scan iteration for the second bootstrap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData_columnSum_le_coefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).coefficient := by
  have hFirstCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H :=
    lt_trans hbetaCutoff
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff_lt_firstBootstrapCutoff
        H)
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData
        H N hN beta hbeta hbetaPos hFirstCutoff B).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
        H beta
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedInfluenceData_columnSum_le_totalCoefficient
      H N hN beta hbeta hbetaPos hFirstCutoff B source

end

end MathlibAnalytic
end MGAP4D
