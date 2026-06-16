import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapClusterRate
import Mathlib.Analysis.Normed.Operator.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A finite Wilson connected-correlation representation through powers of a
volume-dependent transfer operator on one normed state space.

The scalar decay estimate is not assumed. It is generated from a uniform
operator-norm contraction and a uniform bound on the readout/state amplitude. -/
structure FiniteWilsonOSAutomaticExactGapTransferOperatorData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateNormedSpace : NormedSpace ℝ StateSpace]
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  decayAmplitude_nonneg : ∀ O : Observable, 0 ≤ decayAmplitude O
  transferOperator : ℕ → StateSpace →L[ℝ] StateSpace
  correlationState : ℕ → Observable → ℕ → StateSpace
  correlationReadout : ℕ → Observable → StateSpace →L[ℝ] ℝ
  state_succ :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      correlationState n O (Nat.succ r) =
        transferOperator n (correlationState n O r)
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O (correlationState n O r)
  transferOperatorNormBound :
    ∀ n : ℕ, ‖transferOperator n‖ ≤ exactGapClusterContractionRatio
  readoutInitialStateBound :
    ∀ (n : ℕ) (O : Observable),
      ‖correlationReadout n O‖ * ‖correlationState n O 0‖ ≤
        decayAmplitude O
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))

attribute [instance]
  FiniteWilsonOSAutomaticExactGapTransferOperatorData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapTransferOperatorData.stateNormedSpace

/-- Uniform operator-norm contraction gives a geometric bound for every
correlation state. -/
theorem finite_wilson_exact_gap_transfer_state_norm_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖D.correlationState n O r‖ ≤
      exactGapClusterContractionRatio ^ r * ‖D.correlationState n O 0‖ := by
  induction r with
  | zero => simp
  | succ r ihr =>
      rw [D.state_succ n O r]
      calc
        ‖D.transferOperator n (D.correlationState n O r)‖ ≤
            ‖D.transferOperator n‖ * ‖D.correlationState n O r‖ :=
          (D.transferOperator n).le_opNorm _
        _ ≤ exactGapClusterContractionRatio *
              ‖D.correlationState n O r‖ :=
          mul_le_mul_of_nonneg_right
            (D.transferOperatorNormBound n) (norm_nonneg _)
        _ ≤ exactGapClusterContractionRatio *
              (exactGapClusterContractionRatio ^ r *
                ‖D.correlationState n O 0‖) :=
          mul_le_mul_of_nonneg_left ihr
            exact_gap_cluster_contraction_ratio_nonneg
        _ = exactGapClusterContractionRatio ^ Nat.succ r *
              ‖D.correlationState n O 0‖ := by
          rw [pow_succ]
          ring

/-- The transfer-operator representation generates the full finite-volume
exact-gap connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_transfer_operator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r := by
  rw [D.connectedCorrelation_representation n O r]
  calc
    ‖D.correlationReadout n O (D.correlationState n O r)‖ ≤
        ‖D.correlationReadout n O‖ * ‖D.correlationState n O r‖ :=
      (D.correlationReadout n O).le_opNorm _
    _ ≤ ‖D.correlationReadout n O‖ *
          (exactGapClusterContractionRatio ^ r *
            ‖D.correlationState n O 0‖) :=
      mul_le_mul_of_nonneg_left
        (finite_wilson_exact_gap_transfer_state_norm_bound D n O r)
        (norm_nonneg _)
    _ = (‖D.correlationReadout n O‖ * ‖D.correlationState n O 0‖) *
          exactGapClusterContractionRatio ^ r := by
      ring
    _ ≤ D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
      mul_le_mul_of_nonneg_right
        (D.readoutInitialStateBound n O)
        (pow_nonneg exact_gap_cluster_contraction_ratio_nonneg r)

/-- Convert the transfer-operator package into the exact-gap cluster package. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapTransferOperatorData.toExactGapClusterData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W) :
    FiniteWilsonOSAutomaticExactGapClusterData W :=
  { Observable := D.Observable
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    pointwiseConvergence := D.pointwiseConvergence
    uniformExactGapBound := finite_wilson_exact_gap_bound_of_transfer_operator D }

/-- A uniform exact-gap transfer-operator contraction implies continuum
clustering. -/
theorem finite_wilson_exact_gap_transfer_operator_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W) :
    D.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_cluster_passes_to_limit D.toExactGapClusterData

/-- The continuum connected correlation inherits the transfer-operator
exact-gap estimate. -/
theorem finite_wilson_exact_gap_transfer_operator_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapTransferOperatorData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_cluster_continuum_bound D.toExactGapClusterData O r

end

end MathlibAnalytic
end MGAP4D
