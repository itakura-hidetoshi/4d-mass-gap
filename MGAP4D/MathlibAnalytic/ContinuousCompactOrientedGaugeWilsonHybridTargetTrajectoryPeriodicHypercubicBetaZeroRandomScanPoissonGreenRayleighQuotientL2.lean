import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonResidualEnergyNormEquivalenceL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- The Rayleigh quotient of a continuous linear endomorphism on a real inner
product space. The zero vector is intentionally left with the ambient field's
ordinary division convention; all extremal statements below assume a nonzero
vector. -/
noncomputable def continuousLinearMapRayleighQuotient
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (x : E) : ℝ :=
  inner ℝ (T x) x / ‖x‖ ^ 2

/-- Quadratic-form bounds become Rayleigh-quotient bounds at every nonzero
vector. -/
theorem continuousLinearMap_rayleighQuotient_bounds
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (m M : ℝ)
    (x : E)
    (hx : x ≠ 0)
    (hLower : m * ‖x‖ ^ 2 ≤ inner ℝ (T x) x)
    (hUpper : inner ℝ (T x) x ≤ M * ‖x‖ ^ 2) :
    m ≤ continuousLinearMapRayleighQuotient T x ∧
      continuousLinearMapRayleighQuotient T x ≤ M := by
  have hNormPos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hDenPos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hNormPos
  constructor
  · unfold continuousLinearMapRayleighQuotient
    exact (le_div_iff₀ hDenPos).2 hLower
  · unfold continuousLinearMapRayleighQuotient
    exact (div_le_iff₀ hDenPos).2 hUpper

/-- An eigenvector has Rayleigh quotient equal to its real eigenvalue. -/
theorem continuousLinearMap_rayleighQuotient_eq_of_apply_eq_smul
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (x : E)
    (hx : x ≠ 0)
    (hAction : T x = c • x) :
    continuousLinearMapRayleighQuotient T x = c := by
  unfold continuousLinearMapRayleighQuotient
  rw [hAction, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hDenNe : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  apply (div_eq_iff hDenNe).2
  ring

/-- The Rayleigh quotient of the internal beta-zero Poisson endomorphism. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  continuousLinearMapRayleighQuotient
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
    f

/-- The Rayleigh quotient of the centered Green inverse on `Ω⊥`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) : ℝ :=
  continuousLinearMapRayleighQuotient
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
    f

/-- Internal form of the one-cocoercivity of the actual beta-zero Poisson
endomorphism. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_inner
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
        f‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f)
        f := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      f.property
  have hAmbient :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonOperatorL2_apply_sq_le_quadraticForm_of_inner_vacuum_eq_zero
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hOrthogonal
  change
    ‖((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
          Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
  exact hAmbient

/-- The Poisson Rayleigh quotient of every nonzero centered vector lies in the
sharp interval `[1 / 324, 1]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonRayleighQuotientL2_bounds
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hf : f ≠ 0) :
    ((1 : ℝ) / 324) ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f ≤ 1 := by
  have hOrthogonal :
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
      (f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).1
      f.property
  have hLower :
      ((1 : ℝ) / 324) * ‖f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            f)
          f := by
    change
      ((1 : ℝ) / 324) *
          ‖(f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2 ≤
        inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inv_324_mul_norm_sq_le_randomScanPoissonOperatorL2_quadraticForm_of_inner_vacuum_eq_zero
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
        hOrthogonal
  have hUpper :
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
            f)
          f ≤
        (1 : ℝ) * ‖f‖ ^ 2 := by
    change
      inner ℝ
          ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
              f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
            Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ≤
        (1 : ℝ) *
          ‖(f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)‖ ^ 2
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply,
      one_mul]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_quadraticForm_le_norm_sq
        (f : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
  exact
    continuousLinearMap_rayleighQuotient_bounds
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      ((1 : ℝ) / 324) 1 f hf hLower hUpper

/-- The centered Green Rayleigh quotient of every nonzero centered vector lies
in the sharp interval `[1, 324]`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenRayleighQuotientL2_bounds
    (f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2)
    (hf : f ≠ 0) :
    (1 : ℝ) ≤
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f ≤ 324 := by
  have hCocoercive :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoissonVacuumOrthogonalEndL2_apply_sq_le_inner
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
        f)
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply_centeredGreen_eq_self]
    at hCocoercive
  have hLower :
      (1 : ℝ) * ‖f‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f := by
    calc
      (1 : ℝ) * ‖f‖ ^ 2 = ‖f‖ ^ 2 := by ring
      _ ≤ inner ℝ f
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f) := hCocoercive
      _ = inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f := real_inner_comm _ _
  have hUpperRaw :=
    continuousLinearMap_inner_apply_self_le_opNorm_mul_norm_sq
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      f
  have hUpper :
      inner ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
            f)
          f ≤
        (324 : ℝ) * ‖f‖ ^ 2 := by
    simpa only [
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanCenteredGreenVacuumOrthogonalEndL2_eq_324] using
      hUpperRaw
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
  exact
    continuousLinearMap_rayleighQuotient_bounds
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      1 324 f hf hLower hUpper

/-- A nonzero cardinality-one centered mode is an internal Poisson eigenvector
with eigenvalue `1 / 324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f =
        ((1 : ℝ) / 324) • f := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_vacuumOrthogonal_randomScanPoissonOperatorL2_apply_eq_inv_324_smul
    with ⟨f, hfNe, hAmbient⟩
  refine ⟨f, hfNe, ?_⟩
  apply Subtype.ext
  calc
    ((periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonVacuumOrthogonalEndL2_apply
        f
    _ = ((1 : ℝ) / 324) •
          (f : Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := hAmbient
    _ = ((((1 : ℝ) / 324) • f :
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2) :
        Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
      rfl

/-- A nonzero terminal-cardinality centered mode is fixed by the centered Green
inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_self :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f = f := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨f, hfNe, hPoisson⟩
  refine ⟨f, hfNe, ?_⟩
  have hInverse :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_poisson_eq_self
      f
  rw [hPoisson] at hInverse
  exact hInverse

/-- A nonzero cardinality-one centered mode is multiplied by exactly `324` by
the centered Green inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_324_smul :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f = (324 : ℝ) • f := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanGreenOperatorL2_apply_eq_324_smul
    with ⟨f, hfNe, hfOrthogonal, hGreen⟩
  let fOrthogonal :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 :=
    ⟨f,
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_mem_vacuumOrthogonalSubmoduleL2_iff
        f).2 hfOrthogonal⟩
  have hfOrthogonalNe : fOrthogonal ≠ 0 := by
    intro hZero
    apply hfNe
    have hCoe := congrArg
      (fun x : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2 =>
        (x : Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      hZero
    simpa [fOrthogonal] using hCoe
  have hVacuumZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f = 0 := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      hfOrthogonal, zero_smul]
  refine ⟨fOrthogonal, hfOrthogonalNe, ?_⟩
  apply Subtype.ext
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply]
  change
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2 f -
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanGreenOperatorL2
            f) =
      (324 : ℝ) • f
  rw [hGreen, map_smul, hVacuumZero, smul_zero, sub_zero]

/-- The lower Poisson Rayleigh endpoint `1 / 324` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonRayleighQuotientL2_eq_inv_324 :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f = ((1 : ℝ) / 324) := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_inv_324_smul
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
  exact
    continuousLinearMap_rayleighQuotient_eq_of_apply_eq_smul
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      ((1 : ℝ) / 324) f hfNe hAction

/-- The upper Poisson Rayleigh endpoint `1` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonRayleighQuotientL2_eq_one :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f = 1 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonVacuumOrthogonalEndL2_apply_eq_self
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
  have hActionOne :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
          f = (1 : ℝ) • f := by
    simpa using hAction
  exact
    continuousLinearMap_rayleighQuotient_eq_of_apply_eq_smul
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonVacuumOrthogonalEndL2
      1 f hfNe hActionOne

/-- The lower centered-Green Rayleigh endpoint `1` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenRayleighQuotientL2_eq_one :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f = 1 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_self
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
  have hActionOne :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
          f = (1 : ℝ) • f := by
    simpa using hAction
  exact
    continuousLinearMap_rayleighQuotient_eq_of_apply_eq_smul
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      1 f hfNe hActionOne

/-- The upper centered-Green Rayleigh endpoint `324` is attained. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenRayleighQuotientL2_eq_324 :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f = 324 := by
  rcases
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenVacuumOrthogonalEndL2_apply_eq_324_smul
    with ⟨f, hfNe, hAction⟩
  refine ⟨f, hfNe, ?_⟩
  unfold periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
  exact
    continuousLinearMap_rayleighQuotient_eq_of_apply_eq_smul
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenVacuumOrthogonalEndL2
      324 f hfNe hAction

/-- Structured receipt for the exact Poisson and centered-Green Rayleigh
intervals and their attained endpoints. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenRayleighQuotientL2Receipt :
    Prop where
  poisson_bounds :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 →
      ((1 : ℝ) / 324) ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
            f ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
            f ≤ 1
  green_bounds :
    ∀ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 →
      (1 : ℝ) ≤
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
            f ∧
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
            f ≤ 324
  poisson_lower_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f = ((1 : ℝ) / 324)
  poisson_upper_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRayleighQuotientL2
          f = 1
  green_lower_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f = 1
  green_upper_attained :
    ∃ f : periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumOrthogonalL2,
      f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanCenteredGreenRayleighQuotientL2
          f = 324

/-- The exact beta-zero Poisson and centered-Green Rayleigh-extrema receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenRayleighQuotientL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGreenRayleighQuotientL2Receipt := by
  exact
    { poisson_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonRayleighQuotientL2_bounds
      green_bounds :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanCenteredGreenRayleighQuotientL2_bounds
      poisson_lower_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonRayleighQuotientL2_eq_inv_324
      poisson_upper_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanPoissonRayleighQuotientL2_eq_one
      green_lower_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenRayleighQuotientL2_eq_one
      green_upper_attained :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_exists_nonzero_randomScanCenteredGreenRayleighQuotientL2_eq_324 }

end

end MathlibAnalytic
end MGAP4D
