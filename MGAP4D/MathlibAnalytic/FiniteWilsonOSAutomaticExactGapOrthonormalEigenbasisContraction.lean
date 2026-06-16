import Mathlib.Analysis.InnerProductSpace.PiL2
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteSpectralContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite-volume transfer data diagonalized in an orthonormal eigenbasis.
The spectral weights are no longer independent inputs: they are the squared
basis coefficients, and their normalization follows from finite-dimensional
Parseval. -/
structure FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData
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
  transferSymmetric :
    ∀ (n : ℕ) (x y : StateSpace),
      inner ℝ (transferOperator n x) y =
        inner ℝ (transferOperator n y) x
  SpectralIndex : ℕ → Type
  [spectralFintype : ∀ n : ℕ, Fintype (SpectralIndex n)]
  spectralBasis :
    (n : ℕ) → OrthonormalBasis (SpectralIndex n) ℝ StateSpace
  spectralEnergy : (n : ℕ) → SpectralIndex n → ℝ
  spectralEnergy_ge_exactGap :
    ∀ (n : ℕ) (i : SpectralIndex n),
      exactGapValueReal ≤ spectralEnergy n i
  transferRayleighEigenbasisRepresentation :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (transferOperator n x) x =
        ∑ i : SpectralIndex n,
          (inner ℝ (spectralBasis n i) x) ^ 2 *
            Real.exp (-spectralEnergy n i)
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
  FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData.spectralFintype

/-- The squared coefficient weights of an orthonormal eigenbasis sum to the
squared state norm by finite-dimensional Parseval. -/
theorem finite_wilson_orthonormal_eigenbasis_weight_sum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W)
    (n : ℕ) (x : D.StateSpace) :
    ∑ i : D.SpectralIndex n,
        (inner ℝ (D.spectralBasis n i) x) ^ 2 = ‖x‖ ^ 2 := by
  simpa using OrthonormalBasis.sum_sq_inner_right (D.spectralBasis n) x

/-- An orthonormal eigenbasis presentation generates the finite spectral
package, with nonnegative weights and normalization proved rather than assumed. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData.toFiniteSpectralData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W) :
    FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W :=
  { Observable := D.Observable
    StateSpace := D.StateSpace
    stateNormedAddCommGroup := D.stateNormedAddCommGroup
    stateInnerProductSpace := D.stateInnerProductSpace
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    transferOperator := D.transferOperator
    transferSymmetric := D.transferSymmetric
    SpectralIndex := D.SpectralIndex
    spectralFintype := fun n => inferInstance
    spectralEnergy := D.spectralEnergy
    spectralEnergy_ge_exactGap := D.spectralEnergy_ge_exactGap
    spectralWeight := fun n x i =>
      (inner ℝ (D.spectralBasis n i) x) ^ 2
    spectralWeight_nonneg := by
      intro n x i
      exact sq_nonneg _
    spectralWeight_sum := by
      intro n x
      exact finite_wilson_orthonormal_eigenbasis_weight_sum D n x
    transferRayleighSpectralRepresentation :=
      D.transferRayleighEigenbasisRepresentation
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Orthonormal eigenbasis support above the exact gap generates the transfer
operator contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_orthonormal_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_finite_spectral_data
    D.toFiniteSpectralData n

/-- Orthonormal eigenbasis support above the exact gap generates finite-volume
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_orthonormal_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_finite_spectral_data
    D.toFiniteSpectralData n O r

/-- Orthonormal eigenbasis support above the exact gap passes to continuum
clustering after pointwise convergence. -/
theorem finite_wilson_exact_gap_orthonormal_eigenbasis_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W) :
    D.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_finite_spectral_passes_to_limit
    D.toFiniteSpectralData

/-- The continuum connected correlation inherits the exact-gap estimate from
the orthonormal eigenbasis support condition. -/
theorem finite_wilson_exact_gap_orthonormal_eigenbasis_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_finite_spectral_continuum_bound
    D.toFiniteSpectralData O r

end

end MathlibAnalytic
end MGAP4D
