import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledStationaryFiniteStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledSourceForcingResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanBlockIterateBridge
import Mathlib.Tactic

/-!
# Pin-free stationary terminal residual

The pin-free response-controlled stationary finite-step theorem leaves one
terminal term: the response of a common `k`-boundary random-scan smoothed
observable under two reference laws.

At complete-block times this terminal term is controlled by the existing
fixed-volume Doeblin block theorem.  The key point is that the `k`-boundary
random-scan iterate converges uniformly to its exact `mu_k` stationary mean.
Since its integral under `mu_k` is already exactly that mean, only one
Doeblin residual appears:

  terminal_n <= rho_H(beta)^n * globalOscillation.

There is no factor two.

For the fixed-right target-ratio observable the global oscillation is bounded
by `exp (16 * beta)`.  Combining this terminal estimate with the pin-free
source-forcing resolvent yields a complete-block finite-step response bound
whose nonterminal coefficient is

  18 * eta(beta) * s^2 + exp(16 * beta) * M,

with no distinguished-target pin term.

The Doeblin residual is used only to remove the terminal term at each fixed
finite volume.  It is not treated as a volume-uniform spatial contraction.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance pinFreeResponseControlledStationaryTerminalResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pinFreeResponseControlledStationaryTerminalResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pinFreeResponseControlledStationaryTerminalResidualSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pinFreeResponseControlledStationaryTerminalResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pinFreeResponseControlledStationaryTerminalResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pinFreeResponseControlledStationaryTerminalResidualSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At complete-block times, the terminal discrepancy of the common
`k`-boundary smoothed observable is bounded by one Doeblin residual factor.

The second integral is exactly the stationary mean under the matching
`k`-boundary law, so no second residual factor is needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_terminalResponse_mul_scheduleLength_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hF : StronglyMeasurable F)
    (oscillation : ℝ)
    (hOscillationNonneg : 0 ≤ oscillation)
    (hOscillation :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |F X - F Y| ≤ oscillation)
    (n : ℕ) :
    |(∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k F
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length) A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source h g₂) -
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k F
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length) A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n * oscillation := by
  classical
  let L :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H).length
  let rho :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source h g₂
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let Gn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
      H N hN beta hbeta B target source g₂ k F (n * L)
  let c := ∫ X, F X ∂μk
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source h g₂
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source k g₂
  let A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun _ => 1
  let M : ℝ := oscillation + |F A₀|
  have hMNonneg : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg hOscillationNonneg (abs_nonneg _)
  have hFBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |F X| ≤ M := by
    intro X
    dsimp [M]
    calc
      |F X| = |(F X - F A₀) + F A₀| := by
        congr 1
        ring
      _ ≤ |F X - F A₀| + |F A₀| := abs_add_le _ _
      _ ≤ oscillation + |F A₀| :=
        add_le_add (hOscillation X A₀) le_rfl
  have hFIntK : Integrable F μk := by
    refine Integrable.of_bound hF.aestronglyMeasurable M ?_
    exact Filter.Eventually.of_forall fun X => by
      simpa [Real.norm_eq_abs] using hFBound X
  have hGnStrong : StronglyMeasurable Gn := by
    dsimp [Gn]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
        H N hN beta hbeta B target source g₂ k F hF (n * L)
  have hCenter :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |Gn A - c| ≤ rho ^ n * oscillation := by
    intro A
    have hBlock :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_sub_referenceMean_abs_le
        H N hN beta hbeta B target source k g₂ F hF
        oscillation hOscillationNonneg hOscillation n A
    have hBridge :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_eq_expectationIterate_mul_scheduleLength
        H N hN beta hbeta B target source k g₂ F hF
        oscillation hOscillationNonneg hOscillation n A
    rw [hBridge] at hBlock
    simpa [Gn, c, μk, rho, L] using hBlock
  have hErrNonneg : 0 ≤ rho ^ n * oscillation := by
    exact mul_nonneg (pow_nonneg ENNReal.toReal_nonneg n) hOscillationNonneg
  have hDiffInt : Integrable (fun A => Gn A - c) μh := by
    refine
      Integrable.of_bound
        (hGnStrong.sub stronglyMeasurable_const).aestronglyMeasurable
        (rho ^ n * oscillation) ?_
    exact Filter.Eventually.of_forall fun A => by
      simpa [Real.norm_eq_abs, abs_of_nonneg hErrNonneg] using hCenter A
  have hGnIntH : Integrable Gn μh := by
    have hAux := hDiffInt.add (integrable_const c)
    exact hAux.congr (Filter.Eventually.of_forall fun A => by ring)
  have hAbsDiffInt : Integrable (fun A => |Gn A - c|) μh := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hErrInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          rho ^ n * oscillation)
        μh :=
    integrable_const (rho ^ n * oscillation)
  have hMeanK : (∫ A, Gn A ∂μk) = c := by
    dsimp [Gn, c, μk, L]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_integral_eq
        H N hN beta hbeta B target source g₂ k F hFIntK
        (n *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
  change |(∫ A, Gn A ∂μh) - ∫ A, Gn A ∂μk| ≤ rho ^ n * oscillation
  rw [hMeanK]
  calc
    |(∫ A, Gn A ∂μh) - c| =
        |∫ A, Gn A - c ∂μh| := by
          rw [integral_sub hGnIntH (integrable_const c)]
          simp
    _ ≤ ∫ A, |Gn A - c| ∂μh :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        rho ^ n * oscillation ∂μh := by
          apply integral_mono hAbsDiffInt hErrInt
          intro A
          exact hCenter A
    _ = rho ^ n * oscillation := by simp

/-- The fixed-right target-ratio observable has global pairwise oscillation at
most `exp (16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_globalOscillation_le_exp_sixteen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |(periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta X B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta X B target g₂) -
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Y B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta Y B target g₂)| ≤
      Real.exp (16 * beta) := by
  have hXPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
      H N beta X B target g₁ g₂
  have hYPos :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
      H N beta Y B target g₁ g₂
  have hXBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
      H N hN beta hbeta X B target g₁ g₂
  have hYBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
      H N hN beta hbeta Y B target g₁ g₂
  rw [abs_le]
  constructor <;> linarith

/-- At complete-block times, the terminal term in the remote fixed-right
target-ratio stationary response is bounded by the explicit fixed-volume
Doeblin residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_terminalResponse_mul_scheduleLength_le_exp_sixteen_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    |(∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k
          (fun C =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta C B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta C B target g₂)
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length) A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) -
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g₂ k
          (fun C =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta C B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta C B target g₂)
          (n *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
              H).length) A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n * Real.exp (16 * beta) := by
  let F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₂
  have hF : StronglyMeasurable F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g₁ g₂
  have hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |F X - F Y| ≤ Real.exp (16 * beta) := by
    intro X Y
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_globalOscillation_le_exp_sixteen
        H N hN beta hbeta B target g₁ g₂ X Y
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_terminalResponse_mul_scheduleLength_le
      H N hN beta hbeta B target source g₂ h k F hF
      (Real.exp (16 * beta)) (Real.exp_pos _).le hOsc n
  have hBridgeH :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B hne hNoShare h g₂
  have hBridgeK :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B hne hNoShare k g₂
  rw [hBridgeH, hBridgeK] at hBase
  simpa [F] using hBase

/-- Complete-block finite-step remote response bound obtained by combining the
pin-free source-forcing resolvent with the one-factor terminal residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_pinFreeWeightedResolvent_add_terminalBlockResidual_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    |(∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) -
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n * Real.exp (16 * beta) := by
  let m :=
    n *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_pinFreeResponseControlledAccumulated_add_terminal_of_remote
      H N hN beta hbeta R hRNonneg hResponse B hne hNoShare g₁ g₂ h k m
  have hAccum :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioPinFreeAccumulatedSourceDiscrepancy_le_weightedResolvent
      H beta hbeta s hs target source R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      hCoefficientLtOne m
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_terminalResponse_mul_scheduleLength_le_exp_sixteen_of_remote
      H N hN beta hbeta B hne hNoShare g₁ g₂ h k n
  calc
    |(∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) -
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        m +
      |(∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k
            (fun C =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C B target g₁ /
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C B target g₂)
            m A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source h) target g₂)) -
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g₂ k
            (fun C =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C B target g₁ /
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C B target g₂)
            m A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))| := hFinite
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n * Real.exp (16 * beta) := by
          exact add_le_add hAccum (by simpa [m] using hTerminal)

end

end MathlibAnalytic
end MGAP4D
