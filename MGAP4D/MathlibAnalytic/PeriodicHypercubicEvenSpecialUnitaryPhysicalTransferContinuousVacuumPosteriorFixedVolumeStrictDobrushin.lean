import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRefinedLocalInfluence
import Mathlib.Tactic

/-!
# Fixed-volume strict posterior Dobrushin neighborhood

PR #5179 replaces the plaquette-local fallback value one by a direct
high-temperature coefficient which vanishes at beta = 0.  At zero block depth,
the remote first-bootstrap response radius also vanishes at beta = 0.

For fixed finite spatial side H define the scalar refined influence entry

  c_H(beta; target, source),

using the direct coefficient on plaquette-local pairs and the first-bootstrap
remote coefficient on remote pairs.  Its total finite mass

  alpha_H(beta) = sum_target sum_source c_H(beta; target, source)

is a common upper bound for every row sum.  The entry functions are continuous
in beta, alpha_H(0)=0, and therefore every fixed H has a positive coupling
neighborhood on which alpha_H(beta)<1.

This closes a genuine fixed-volume strict Dobrushin seed.  The cutoff may
depend on H, so this is not yet a volume-uniform mass-gap statement.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorFixedVolumeStrictDobrushinSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Zero-block-depth scalar refined influence entry. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
    H beta
    (fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta 0)
    target source

/-- The actual first-bootstrap refined data at block depth zero have exactly
the scalar entry above, independently of the posterior boundary. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData_zeroDepth_influence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData
      H N hN beta hbeta 0 B).influence target source =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
        H beta target source := by
  rfl

/-- At zero block depth the first-bootstrap radius simplifies before any
Doeblin residual factor enters. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zeroDepth_eq
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta 0 =
      Real.exp (8 * beta) *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
            beta /
        Real.exp (-8 * beta) := by
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius]

/-- The zero-depth first-bootstrap response radius is continuous in beta. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zeroDepth
    (H : ℕ) :
    Continuous
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
          H beta 0) := by
  have hWidth :
      Continuous
        (fun beta : ℝ =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
            beta) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
    fun_prop
  have hNum :
      Continuous
        (fun beta : ℝ =>
          Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
              beta) := by
    exact
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hWidth
  have hDen :
      Continuous (fun beta : ℝ => Real.exp (-8 * beta)) := by
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hQuot :
      Continuous
        (fun beta : ℝ =>
          (Real.exp (8 * beta) *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
                beta) /
            Real.exp (-8 * beta)) :=
    hNum.div hDen (fun beta => Real.exp_ne_zero (-8 * beta))
  exact
    hQuot.congr fun beta =>
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zeroDepth_eq
        H beta).symm

/-- The direct local coefficient is continuous in beta. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence :
    Continuous
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
  let e : ℝ → ℝ := fun beta => Real.exp (32 * beta)
  have he : Continuous e := by
    dsimp [e]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact
    (he.sub continuous_const).div
      (he.add continuous_const)
      (fun beta => ne_of_gt (by dsimp [e]; positivity))

/-- The remote response-generated coefficient at zero block depth is
continuous in beta. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_firstBootstrap_zeroDepth
    (H : ℕ) :
    Continuous
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
          beta
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
            H beta 0)) := by
  let eps : ℝ → ℝ := fun beta =>
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
      H beta 0
  have heps : Continuous eps := by
    dsimp [eps]
    exact
      continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_zeroDepth
        H
  let floor : ℝ → ℝ := fun beta => Real.exp (-8 * beta)
  have hfloor : Continuous floor := by
    dsimp [floor]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hratio :
      Continuous (fun beta => eps beta / floor beta) :=
    heps.div hfloor (fun beta => by dsimp [floor]; exact Real.exp_ne_zero _)
  let R : ℝ → ℝ := fun beta => 2 * (eps beta / floor beta)
  have hR : Continuous R := by
    dsimp [R]
    exact continuous_const.mul hratio
  let E : ℝ → ℝ := fun beta => Real.exp (R beta)
  have hE : Continuous E := by
    dsimp [E]
    exact Real.continuous_exp.comp hR
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
  dsimp [eps, floor, R, E]
  exact
    (hE.sub continuous_const).div
      (hE.add continuous_const)
      (fun beta => ne_of_gt (by dsimp [E]; positivity))

/-- Every fixed zero-depth refined influence entry is continuous in beta. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
          H beta target source) := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp only [hlocal, if_true]
      exact
        continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
    · simp only [hlocal, if_false]
      exact
        continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_firstBootstrap_zeroDepth
          H

/-- The zero-depth refined entry vanishes at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence_zero
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
        H 0 target source = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp [
        hlocal,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence]
    · simp [
        hlocal,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence]

/-- Row sum of the zero-depth refined first-bootstrap influence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum
    (H : ℕ)
    (beta : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
      H beta target source

/-- Total finite influence mass, used as a common row coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
    (H : ℕ)
    (beta : ℝ) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
        H beta target source

/-- The total fixed-volume coefficient is continuous in beta. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
    (H : ℕ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H) := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
  exact
    continuous_finsetSum Finset.univ fun target _ =>
      continuous_finsetSum Finset.univ fun source _ =>
        continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
          H target source

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_zero
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H 0 = 0 := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient]

/-- The total coefficient is nonnegative for nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
  apply Finset.sum_nonneg
  intro target _hTarget
  apply Finset.sum_nonneg
  intro source _hSource
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
      H beta hbeta
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
          H beta 0)
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_nonneg
          H beta hbeta 0)
      target source

/-- Every row is bounded by the total finite influence coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum_le_totalCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum
        H beta target ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
  apply
    Finset.single_le_sum
      (fun t _ =>
        Finset.sum_nonneg fun s _ => by
          unfold
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
          exact
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
              H beta hbeta
              (fun _target _source =>
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
                  H beta 0)
              (fun _target _source =>
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_nonneg
                  H beta hbeta 0)
              t s)
      (Finset.mem_univ target)

/-- A continuous scalar coefficient vanishing at zero is below one on some
positive neighborhood of zero. -/
private theorem continuous_zero_exists_positive_lt_one
    (f : ℝ → ℝ)
    (hf : Continuous f)
    (h0 : f 0 = 0) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      ∀ beta : ℝ, 0 < beta → beta < cutoff → f beta < 1 := by
  have hAt : ContinuousAt f 0 := hf.continuousAt
  rw [Metric.continuousAt_iff] at hAt
  obtain ⟨delta, hDelta, hControl⟩ :=
    hAt 1 (by norm_num)
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

/-- Every fixed finite side has a positive high-temperature interval on which
the refined first-bootstrap total coefficient is strictly below one. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
    (H : ℕ) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      ∀ beta : ℝ, 0 < beta → beta < cutoff →
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
            H beta < 1 := by
  exact
    continuous_zero_exists_positive_lt_one
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H)
      (continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_zero
        H)

/-- Canonically selected fixed-volume strict Dobrushin cutoff. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
    (H : ℕ) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
      H)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_pos
    (H : ℕ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
        H :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
      H)).1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
      H)).2
    beta hbeta hbetaCutoff

/-- Strict continuous-vacuum posterior Dobrushin data. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    extends
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  rowSum_le_coefficient :
    ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        influence target source ≤ coefficient
  coefficient_lt_one : coefficient < 1

/-- The fixed-volume cutoff upgrades the refined first-bootstrap matrix to
strict posterior Dobrushin data at every boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
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
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
      H N hN beta hbeta B := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRefinedInfluenceData
      H N hN beta hbeta 0 B
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  refine
    { toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData := D
      coefficient := coefficient
      coefficient_nonneg := ?_
      rowSum_le_coefficient := ?_
      coefficient_lt_one := ?_ }
  · dsimp [coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_nonneg
        H beta hbeta
  · intro target
    dsimp [D, coefficient]
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedRowSum_le_totalCoefficient
        H beta hbeta target
  · dsimp [coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
        H beta hbetaPos hbetaCutoff

/-- Every concrete row sum of the selected fixed-volume posterior matrix is
strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData_rowSum_lt_one
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
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) < 1 := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  exact lt_of_le_of_lt (D.rowSum_le_coefficient target) D.coefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
