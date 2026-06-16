import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapTransferOperator
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Hilbert coefficient input for the finite Wilson transfer contraction.

The inner-product structure is the unique source of the real normed-space
instance, preventing distinct `NormedSpace` dictionaries from appearing in the
stored operator and in the matrix-coefficient theorem. -/
structure FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateInnerProductSpace : InnerProductSpace ℝ StateSpace]
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
  matrixCoefficientBound :
    ∀ (n : ℕ) (x y : StateSpace),
      ‖x‖ = 1 → ‖y‖ = 1 →
        RCLike.re (inner ℝ (transferOperator n x) y) ≤
          exactGapClusterContractionRatio
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
  FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData.stateInnerProductSpace

/-- Uniform control of all unit Hilbert matrix coefficients controls the
operator norm. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_matrix_coefficients
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le
    (𝕜 := ℝ)
    (E := D.StateSpace)
    (F := D.StateSpace)
    (T := D.transferOperator n)
    exact_gap_cluster_contraction_ratio_nonneg
  intro x y hx hy
  exact D.matrixCoefficientBound n x y hx hy

/-- Forget the Hilbert presentation only after deriving the operator-norm
contraction required by the transfer-state cluster argument. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData.toTransferOperatorData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W) :
    FiniteWilsonOSAutomaticExactGapTransferOperatorData W :=
  { Observable := D.Observable
    StateSpace := D.StateSpace
    stateNormedAddCommGroup := D.stateNormedAddCommGroup
    stateNormedSpace := D.stateInnerProductSpace.toNormedSpace
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    transferOperator := D.transferOperator
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    transferOperatorNormBound :=
      finite_wilson_exact_gap_operator_norm_bound_of_matrix_coefficients D
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Hilbert matrix-coefficient contraction generates the full finite-volume
exact-gap connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_hilbert_matrix_contraction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_transfer_operator
    D.toTransferOperatorData n O r

/-- Hilbert matrix-coefficient contraction implies continuum clustering after
pointwise convergence. -/
theorem finite_wilson_exact_gap_hilbert_matrix_contraction_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W) :
    D.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_transfer_operator_passes_to_limit
    D.toTransferOperatorData

/-- The continuum connected correlation inherits the exact-gap estimate
constructed from the Hilbert matrix-coefficient bound. -/
theorem finite_wilson_exact_gap_hilbert_matrix_contraction_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHilbertMatrixContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_transfer_operator_continuum_bound
    D.toTransferOperatorData O r

end

end MathlibAnalytic
end MGAP4D
