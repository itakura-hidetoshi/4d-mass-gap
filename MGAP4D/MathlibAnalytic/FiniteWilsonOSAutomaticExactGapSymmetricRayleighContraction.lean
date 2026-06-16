import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapHilbertMatrixContraction
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A symmetric Hilbert-space transfer operator controlled only through its
unit-sphere Rayleigh quotients.

For symmetric operators, mathlib identifies the operator norm with the supremum
of the absolute Rayleigh quotient. Thus no off-diagonal matrix-coefficient bound
is required at this layer. -/
structure FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData
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
  transferOperatorSymmetric : ∀ n : ℕ, (transferOperator n).IsSymmetric
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
  unitRayleighAbsBound :
    ∀ (n : ℕ) (x : StateSpace),
      ‖x‖ = 1 →
        |(transferOperator n).rayleighQuotient x| ≤
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
  FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.stateInnerProductSpace

/-- A unit-sphere Rayleigh bound extends to every vector by scale invariance. -/
theorem finite_wilson_exact_gap_rayleigh_abs_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (n : ℕ) (x : D.StateSpace) :
    |(D.transferOperator n).rayleighQuotient x| ≤
      exactGapClusterContractionRatio := by
  by_cases hx : x = 0
  · simp [hx, exact_gap_cluster_contraction_ratio_nonneg]
  · let c : ℝ := ‖x‖⁻¹
    have hc : c ≠ 0 := by
      exact inv_ne_zero (norm_ne_zero_iff.mpr hx)
    have hcx : ‖c • x‖ = 1 := by
      simp [c, hx]
    have h := D.unitRayleighAbsBound n (c • x) hcx
    rwa [(D.transferOperator n).rayleigh_smul x hc] at h

/-- Symmetry plus the unit Rayleigh bound gives the exact-gap operator-norm
contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_symmetric_rayleigh
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio := by
  rw [(D.transferOperator n).norm_eq_iSup_rayleighQuotient
    (D.transferOperatorSymmetric n)]
  exact ciSup_le fun x => finite_wilson_exact_gap_rayleigh_abs_bound D n x

/-- Convert the symmetric Rayleigh package to the transfer-operator package. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData.toTransferOperatorData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W) :
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
      finite_wilson_exact_gap_operator_norm_bound_of_symmetric_rayleigh D
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Symmetric Rayleigh contraction generates the finite exact-gap correlation
bound. -/
theorem finite_wilson_exact_gap_bound_of_symmetric_rayleigh_contraction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_transfer_operator
    D.toTransferOperatorData n O r

/-- Symmetric Rayleigh contraction implies continuum clustering. -/
theorem finite_wilson_exact_gap_symmetric_rayleigh_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W) :
    D.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_transfer_operator_passes_to_limit
    D.toTransferOperatorData

/-- The continuum correlation inherits the symmetric-Rayleigh exact-gap rate. -/
theorem finite_wilson_exact_gap_symmetric_rayleigh_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSymmetricRayleighContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_transfer_operator_continuum_bound
    D.toTransferOperatorData O r

end

end MathlibAnalytic
end MGAP4D
