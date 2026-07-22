import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonResidualErrorRepresentationL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- For a contractive continuous linear operator, the residual norm is bounded
above by the norm of the exact-solution error. -/
theorem continuousLinearMap_norm_residual_le_norm_solution_sub_of_contractive
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E)
    (b uStar u : E)
    (hSolution : A uStar = b)
    (hContractive : ∀ x : E, ‖A x‖ ≤ ‖x‖) :
    ‖continuousLinearMapResidual A b u‖ ≤ ‖uStar - u‖ := by
  rw [continuousLinearMap_residual_eq_apply_solution_sub A b uStar u hSolution]
  exact hContractive (uStar - u)

/-- On the actual beta-zero Gibbs-vacuum orthogonal sector, the Poisson
operator is norm-contractive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_le_norm_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ ≤ ‖f‖ := by
  have hDecomposition :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_positive_fluctuationCardinalityProjectorL2_apply_eq_of_inner_vacuum_eq_zero
      f hOrthogonal
  have hAction :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        ∑ k ∈ Finset.range 324,
          (((k + 1 : ℕ) : ℝ) / 324) •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
    calc
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (∑ k ∈ Finset.range 324,
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        rw [hDecomposition]
      _ = ∑ k ∈ Finset.range 324,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f) := by
        simp only [map_sum]
      _ = ∑ k ∈ Finset.range 324,
          (((k + 1 : ℕ) : ℝ) / 324) •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f := by
        apply Finset.sum_congr rfl
        intro k hk
        have hUpper : k + 1 ≤ 324 := by
          simp only [Finset.mem_range] at hk
          omega
        let component : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f
        have hRandomPow :=
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPowL2_apply_eq_smul_of_mem_cardinalityEigenspace
            (k + 1) 1 component
            (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_mem_randomScanCardinalityEigenspaceL2
              (k + 1) hUpper f)
        have hRandom :
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
                component =
              (1 - (((k + 1 : ℕ) : ℝ) / 324)) • component := by
          simpa [component] using hRandomPow
        change
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
              component =
            (((k + 1 : ℕ) : ℝ) / 324) • component
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
          hRandom]
        calc
          component -
              (1 - (((k + 1 : ℕ) : ℝ) / 324)) • component =
            (1 - (1 - (((k + 1 : ℕ) : ℝ) / 324))) • component := by
              rw [sub_smul, one_smul]
          _ = (((k + 1 : ℕ) : ℝ) / 324) • component := by
              congr 1
              ring
  have hFamilyOrth :
      ∀ i ∈ Finset.range 324, ∀ j ∈ Finset.range 324, i ≠ j →
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (i + 1) f)
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (j + 1) f) = 0 := by
    intro i _hi j _hj hij
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_fluctuationCardinalityProjectorL2_same_input_eq_zero_of_ne
        (i + 1) (j + 1) (by omega) f
  have hCoeff :
      ∀ k ∈ Finset.range 324,
        |(((k + 1 : ℕ) : ℝ) / 324)| ≤ (1 : ℝ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hUpperNat : k + 1 ≤ 324 := by omega
    have hUpperReal : (((k + 1 : ℕ) : ℝ) ≤ 324) := by
      exact_mod_cast hUpperNat
    have hNonneg : 0 ≤ (((k + 1 : ℕ) : ℝ) / 324) := by
      positivity
    rw [abs_of_nonneg hNonneg]
    nlinarith
  have hWeightedBound :=
    finset_norm_sum_smul_le_mul_norm_sum_of_pairwise_inner_eq_zero
      (s := Finset.range 324)
      (v := fun k =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f)
      (a := fun k => (((k + 1 : ℕ) : ℝ) / 324))
      (r := (1 : ℝ))
      hFamilyOrth hCoeff (by norm_num)
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ =
      ‖∑ k ∈ Finset.range 324,
        (((k + 1 : ℕ) : ℝ) / 324) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ := congrArg norm hAction
    _ ≤ (1 : ℝ) *
        ‖∑ k ∈ Finset.range 324,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ := hWeightedBound
    _ = ‖f‖ := by rw [hDecomposition, one_mul]

/-- Bundled pointwise contraction of the internal Poisson endomorphism on
`Ω⊥`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_le_norm
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        f‖ ≤ ‖f‖ := by
  change
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
      ‖(f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_le_norm_of_inner_vacuum_eq_zero
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      ((periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
        f.property)

/-- The internal Poisson operator norm is at most one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_le_one :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2‖ ≤
      1 := by
  apply
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2.opNorm_le_bound
      (by norm_num)
  intro f
  simpa using
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_le_norm
      f

/-- A nonzero terminal-cardinality vector is fixed by the internal Poisson
endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f = f := by
  have hPoint :
      (0 : ℝ) ∈
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPointSpectrumL2 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPointSpectrumL2_eq_allowed_affine_grid]
    refine ⟨⟨324, by omega⟩, ?_⟩
    norm_num
  change ∃ w : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    w ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          w = (0 : ℝ) • w at hPoint
  rcases hPoint with ⟨w, hwNe, hRandom⟩
  have hRandomZero :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.randomScanHeatBathL2
          w = 0 := by
    simpa using hRandom
  have hPoisson :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          w = w := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply,
      hRandomZero, sub_zero]
  have hwMem :
      w ∈ periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalSubmoduleL2 := by
    rw [← hPoisson]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_mem_vacuumOrthogonalSubmoduleL2
        w
  let wOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨w, hwMem⟩
  have hwOrthogonalNe : wOrthogonal ≠ 0 := by
    intro hZero
    apply hwNe
    have hCoe := congrArg
      (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (x : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hZero
    simpa [wOrthogonal] using hCoe
  refine ⟨wOrthogonal, hwOrthogonalNe, ?_⟩
  apply Subtype.ext
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        w = w
  exact hPoisson

/-- The internal Poisson operator norm is at least one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_le_norm_randomScanPoissonVacuumOrthogonalEndL2 :
    (1 : ℝ) ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2‖ := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨f, hfNe, hAction⟩
  have hNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hfNe
  have hFundamental :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2.le_opNorm
      f
  rw [hAction] at hFundamental
  nlinarith [
    ContinuousLinearMap.opNorm_nonneg
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2]

/-- The exact operator norm of the internal beta-zero Poisson map is one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_eq_one :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2‖ =
      1 := by
  exact le_antisymm
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_le_one
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_one_le_norm_randomScanPoissonVacuumOrthogonalEndL2

/-- The standard operator-norm condition number of the actual internal Poisson
automorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonConditionNumberL2 :
    ℝ :=
  ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2‖ *
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2‖

/-- The exact finite-volume beta-zero Poisson condition number is `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonConditionNumberL2_eq_324 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonConditionNumberL2 =
      324 := by
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonConditionNumberL2
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324]
  norm_num

/-- The actual centered residual is bounded above by the canonical solution
error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_le_norm_generalizedInverse_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f -
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_le_norm_of_inner_vacuum_eq_zero
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f -
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_generalizedInverse_sub_subtype_eq_zero
        f u)

/-- Sharp two-sided norm equivalence between the actual residual and the
canonical solution error. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_norm_equivalence
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 324) *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ∧
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ≤
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f -
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ := by
  constructor
  · rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_le_norm_randomScanPoissonOperatorL2_apply_of_inner_vacuum_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_generalizedInverse_sub_subtype_eq_zero
          f u)
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_le_norm_generalizedInverse_sub
        f u

/-- Structured receipt for exact beta-zero Poisson conditioning and residual
norm equivalence. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualNormEquivalenceL2Receipt :
    Prop where
  poisson_norm_eq_one :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2‖ =
      1
  inverse_norm_eq_324 :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2‖ =
      324
  condition_number_eq_324 :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonConditionNumberL2 =
      324
  residual_norm_equivalence :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ((1 : ℝ) / 324) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f -
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ≤
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖
  lower_factor_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalRestrictionL2
          f‖ =
        ((1 : ℝ) / 324) * ‖f‖
  upper_factor_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f = f

/-- The exact beta-zero Poisson conditioning and residual-equivalence receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualNormEquivalenceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualNormEquivalenceL2Receipt := by
  refine
    { poisson_norm_eq_one :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_eq_one
      inverse_norm_eq_324 :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324
      condition_number_eq_324 :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonConditionNumberL2_eq_324
      residual_norm_equivalence := ?_
      lower_factor_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_norm_randomScanPoissonVacuumOrthogonalRestrictionL2_apply_eq_inv_324_mul_norm
      upper_factor_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self }
  intro f u
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_norm_equivalence
      f u

end

end MathlibAnalytic
end MGAP4D
