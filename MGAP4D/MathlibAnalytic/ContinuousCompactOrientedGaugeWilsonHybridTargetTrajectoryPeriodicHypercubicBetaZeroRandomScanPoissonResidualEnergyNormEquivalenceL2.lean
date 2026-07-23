import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonDirichletEnergyNormEquivalenceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The inner product of a finite orthogonal weighted sum with the corresponding
unweighted sum is the weighted sum of squared norms. -/
theorem finset_inner_sum_smul_sum_eq_sum_mul_norm_sq_of_pairwise_inner_eq_zero
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → V)
    (a : ι → ℝ)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    inner ℝ (∑ i ∈ s, a i • v i) (∑ i ∈ s, v i) =
      ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      have hTail :
          ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0 := by
        intro i hi j hj hij
        exact hOrth i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      have hHeadTail : inner ℝ (v k) (∑ i ∈ s, v i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        apply hOrth k (Finset.mem_insert_self k s)
          i (Finset.mem_insert_of_mem hi)
        intro hki
        subst i
        exact hk hi
      have hWeightedHeadTail :
          inner ℝ (a k • v k) (∑ i ∈ s, v i) = 0 := by
        rw [real_inner_smul_left, hHeadTail, mul_zero]
      have hWeightedTailHead :
          inner ℝ (∑ i ∈ s, a i • v i) (v k) = 0 := by
        rw [sum_inner]
        apply Finset.sum_eq_zero
        intro i hi
        rw [real_inner_smul_left]
        have hik : i ≠ k := by
          intro hik
          subst i
          exact hk hi
        rw [hOrth i (Finset.mem_insert_of_mem hi)
          k (Finset.mem_insert_self k s) hik, mul_zero]
      calc
        inner ℝ (∑ i ∈ insert k s, a i • v i)
            (∑ i ∈ insert k s, v i) =
          inner ℝ (a k • v k + ∑ i ∈ s, a i • v i)
            (v k + ∑ i ∈ s, v i) := by
              rw [Finset.sum_insert hk, Finset.sum_insert hk]
        _ = inner ℝ (a k • v k) (v k) +
            inner ℝ (∑ i ∈ s, a i • v i) (∑ i ∈ s, v i) := by
              rw [inner_add_left, inner_add_right, inner_add_right,
                hWeightedHeadTail, hWeightedTailHead, add_zero, zero_add]
        _ = a k * ‖v k‖ ^ 2 + ∑ i ∈ s, a i * ‖v i‖ ^ 2 := by
              rw [real_inner_smul_left, real_inner_self_eq_norm_sq, ih hTail]
        _ = ∑ i ∈ insert k s, a i * ‖v i‖ ^ 2 := by
              rw [Finset.sum_insert hk]

/-- A finite orthogonal spectral sum with coefficients in `[0, 1]` is
one-cocoercive: its squared norm is bounded by its pairing with the unweighted
sum. -/
theorem finset_norm_sum_smul_sq_le_inner_sum_smul_sum_of_pairwise_inner_eq_zero
    {ι : Type*}
    [DecidableEq ι]
    (s : Finset ι)
    (v : ι → V)
    (a : ι → ℝ)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0)
    (hNonneg : ∀ i ∈ s, 0 ≤ a i)
    (hLeOne : ∀ i ∈ s, a i ≤ 1) :
    ‖∑ i ∈ s, a i • v i‖ ^ 2 ≤
      inner ℝ (∑ i ∈ s, a i • v i) (∑ i ∈ s, v i) := by
  have hWeightedOrth :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        inner ℝ (a i • v i) (a j • v j) = 0 := by
    intro i hi j hj hij
    rw [real_inner_smul_left, real_inner_smul_right,
      hOrth i hi j hj hij, mul_zero, mul_zero]
  have hNorm :=
    finset_norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
      s (fun i => a i • v i) hWeightedOrth
  have hInner :=
    finset_inner_sum_smul_sum_eq_sum_mul_norm_sq_of_pairwise_inner_eq_zero
      s v a hOrth
  rw [hNorm, hInner]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul, abs_of_nonneg (hNonneg i hi)]
  have hCoeffSq : a i ^ 2 ≤ a i := by
    have hProduct : 0 ≤ a i * (1 - a i) :=
      mul_nonneg (hNonneg i hi) (sub_nonneg.mpr (hLeOne i hi))
    nlinarith
  calc
    (a i * ‖v i‖) ^ 2 = a i ^ 2 * ‖v i‖ ^ 2 := by ring
    _ ≤ a i * ‖v i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCoeffSq (sq_nonneg ‖v i‖)

/-- On the actual Gibbs-vacuum orthogonal sector, the beta-zero Poisson operator
is one-cocoercive. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_quadraticForm_of_inner_vacuum_eq_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f := by
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
        rw [sub_smul, one_smul]
        abel
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
  have hCoeffNonneg :
      ∀ k ∈ Finset.range 324,
        0 ≤ (((k + 1 : ℕ) : ℝ) / 324) := by
    intro k _hk
    positivity
  have hCoeffLeOne :
      ∀ k ∈ Finset.range 324,
        (((k + 1 : ℕ) : ℝ) / 324) ≤ 1 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hUpperNat : k + 1 ≤ 324 := by omega
    have hUpperReal : (((k + 1 : ℕ) : ℝ) ≤ 324) := by
      exact_mod_cast hUpperNat
    nlinarith
  have hCocoercive :=
    finset_norm_sum_smul_sq_le_inner_sum_smul_sum_of_pairwise_inner_eq_zero
      (s := Finset.range 324)
      (v := fun k =>
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          (k + 1) f)
      (a := fun k => (((k + 1 : ℕ) : ℝ) / 324))
      hFamilyOrth hCoeffNonneg hCoeffLeOne
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        f‖ ^ 2 =
      ‖∑ k ∈ Finset.range 324,
        (((k + 1 : ℕ) : ℝ) / 324) •
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f‖ ^ 2 := congrArg (fun g => ‖g‖ ^ 2) hAction
    _ ≤ inner ℝ
        (∑ k ∈ Finset.range 324,
          (((k + 1 : ℕ) : ℝ) / 324) •
            periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              (k + 1) f)
        (∑ k ∈ Finset.range 324,
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            (k + 1) f) := hCocoercive
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f)
        f := by rw [← hAction, hDecomposition]

/-- The generalized-inverse quadratic form of every actual residual dominates
its squared norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_sq_le_generalizedInverse_residual_quadraticForm
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGeneralizedInverseL2_apply_residual_eq_generalizedInverse_sub,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonResidualL2_eq_poisson_apply_generalizedInverse_sub]
  calc
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f -
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_quadraticForm_of_inner_vacuum_eq_zero
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_generalizedInverse_sub_subtype_eq_zero
          f u)
    _ = inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
            f -
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f -
            (u : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) ) :=
      real_inner_comm _ _

/-- The actual Dirichlet energy gap is bounded below by one half of the squared
residual norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_half_mul_norm_residual_sq_le_randomScanPoissonDirichletEnergyL2_sub_canonical
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 2) *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_half_generalizedInverse_residual_quadraticForm]
  exact mul_le_mul_of_nonneg_left
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_sq_le_generalizedInverse_residual_quadraticForm
      f u)
    (by norm_num)

/-- Sharp two-sided residual equivalence for the actual Dirichlet energy gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_residual_norm_equivalence
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ((1 : ℝ) / 2) *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f u -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) ≤
      162 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_half_mul_norm_residual_sq_le_randomScanPoissonDirichletEnergyL2_sub_canonical
      f u,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_le_162_mul_norm_residual_sq
      f u⟩

/-- The actual Green maximum gap is bounded below by the squared residual norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_residual_sq_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_eq_generalizedInverse_residual_quadraticForm]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonResidualL2_sq_le_generalizedInverse_residual_quadraticForm
      f u

/-- Sharp two-sided residual equivalence for the actual Green maximum gap. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_residual_norm_equivalence
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
        f u‖ ^ 2 ≤
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u ∧
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
            f) -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
          f u ≤
      324 *
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_residual_sq_le_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub
      f u,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_le_324_mul_norm_residual_sq
      f u⟩

/-- A nonzero cardinality-one centered mode has Poisson eigenvalue `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_randomScanPoissonOperatorL2_apply_eq_inv_324_smul :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        ((1 : ℝ) / 324) •
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_inner_vacuum_eq_zero_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨w, hwNe, hwOrthogonal, hAction⟩
  let u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨w,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        w).2 hwOrthogonal⟩
  refine ⟨u, ?_, ?_⟩
  · intro hu
    apply hwNe
    have hCoe := congrArg
      (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (z : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hu
    simpa only [u] using hCoe
  · simpa only [u] using hAction

/-- A nonzero terminal-cardinality centered mode has Poisson eigenvalue one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_randomScanPoissonOperatorL2_apply_eq_self :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨u, huNe, hInternal⟩
  refine ⟨u, huNe, ?_⟩
  have hCoe := congrArg
    (fun z : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
      (z : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
    hInternal
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
        (u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
      ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply
        u).symm
    _ = (u : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := hCoe

/-- The lower residual Dirichlet factor `1 / 2` is attained by a nonzero
terminal-cardinality centered mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_half_mul_norm_residual_sq :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 =
        ((1 : ℝ) / 2) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_randomScanPoissonOperatorL2_apply_eq_self
    with ⟨u, huNe, hAction⟩
  have hCanonicalZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    exact map_zero
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_quadraticGap
      (0 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      u
  rw [hCanonicalZero] at hGap
  have hZeroCoe :
      ((0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    rfl
  rw [hZeroCoe, sub_zero, hAction, real_inner_self_eq_norm_sq] at hGap
  have hResidual :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          u =
        -(u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
      continuousLinearMapResidual
    rw [map_zero, hAction, zero_sub]
  refine ⟨u, huNe, ?_⟩
  rw [hResidual, norm_neg]
  exact hGap

/-- The upper residual Dirichlet factor `162` is attained by a nonzero
cardinality-one centered mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_162_mul_norm_residual_sq :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 =
        162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨u, huNe, hAction⟩
  have hCanonicalZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    exact map_zero
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
  have hGap :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_eq_quadraticGap
      (0 : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      u
  rw [hCanonicalZero] at hGap
  have hZeroCoe :
      ((0 : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    rfl
  rw [hZeroCoe, sub_zero, hAction, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hGap
  have hResidual :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          u =
        -(((1 : ℝ) / 324) •
          (u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)) := by
    unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
      continuousLinearMapResidual
    rw [map_zero, hAction, zero_sub]
  refine ⟨u, huNe, ?_⟩
  rw [hResidual, norm_neg, norm_smul, abs_of_nonneg (by norm_num)]
  calc
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 =
      ((1 : ℝ) / 648) *
        ‖(u : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 := by
        nlinarith [hGap]
    _ = 162 *
        (((1 : ℝ) / 324) *
          ‖(u : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖) ^ 2 := by
      ring

/-- The lower residual Green factor `1` is attained by a nonzero
terminal-cardinality centered mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonGreenVariationalFunctionalL2_zero_maxGap_eq_norm_residual_sq :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          u‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_half_mul_norm_residual_sq
    with ⟨u, huNe, hEnergy⟩
  refine ⟨u, huNe, ?_⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy]
  nlinarith

/-- The upper residual Green factor `324` is attained by a nonzero
cardinality-one centered mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonGreenVariationalFunctionalL2_zero_maxGap_eq_324_mul_norm_residual_sq :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u =
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_162_mul_norm_residual_sq
    with ⟨u, huNe, hEnergy⟩
  refine ⟨u, huNe, ?_⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_eq_neg_two_mul_dirichletEnergy]
  nlinarith

/-- Structured receipt for the sharp beta-zero residual-energy equivalences. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualEnergyNormEquivalenceL2Receipt :
    Prop where
  poisson_cocoercive :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          f = 0 →
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            f)
          f
  dirichlet_residual_equivalence :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ((1 : ℝ) / 2) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) ≤
        162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2
  green_residual_equivalence :
    ∀ (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      (u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2),
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          f u‖ ^ 2 ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCanonicalPoissonSolutionToVacuumOrthogonalL2
              f) -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            f u ≤
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            f u‖ ^ 2
  dirichlet_lower_attained :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 =
        ((1 : ℝ) / 2) *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2
  dirichlet_upper_attained :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonDirichletEnergyL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 =
        162 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2
  green_lower_attained :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u =
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
          (0 : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          u‖ ^ 2
  green_upper_attained :
    ∃ u : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      u ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            0 -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenVariationalFunctionalL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u =
        324 *
          ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualL2
            (0 : Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
            u‖ ^ 2

/-- The sharp beta-zero residual-energy equivalence receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualEnergyNormEquivalenceL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonResidualEnergyNormEquivalenceL2Receipt := by
  exact
    { poisson_cocoercive :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_quadraticForm_of_inner_vacuum_eq_zero
      dirichlet_residual_equivalence :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonDirichletEnergyL2_sub_canonical_residual_norm_equivalence
      green_residual_equivalence :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonGreenVariationalFunctionalL2_canonical_sub_residual_norm_equivalence
      dirichlet_lower_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_half_mul_norm_residual_sq
      dirichlet_upper_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonDirichletEnergyL2_zero_gap_eq_162_mul_norm_residual_sq
      green_lower_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonGreenVariationalFunctionalL2_zero_maxGap_eq_norm_residual_sq
      green_upper_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonGreenVariationalFunctionalL2_zero_maxGap_eq_324_mul_norm_residual_sq }

end

end MathlibAnalytic
end MGAP4D
