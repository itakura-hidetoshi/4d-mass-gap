import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapPositiveRayleighContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite-volume transfer data presented by a finite spectral decomposition.
The centered state sector has nonnegative spectral weights, total weight
`‖x‖²`, and every contributing energy lies above the public exact gap. -/
structure FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData
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
  spectralFintype : ∀ n : ℕ, Fintype (SpectralIndex n)
  spectralEnergy : (n : ℕ) → SpectralIndex n → ℝ
  spectralEnergy_ge_exactGap :
    ∀ (n : ℕ) (i : SpectralIndex n),
      exactGapValueReal ≤ spectralEnergy n i
  spectralWeight :
    (n : ℕ) → StateSpace → SpectralIndex n → ℝ
  spectralWeight_nonneg :
    ∀ (n : ℕ) (x : StateSpace) (i : SpectralIndex n),
      0 ≤ spectralWeight n x i
  spectralWeight_sum :
    ∀ (n : ℕ) (x : StateSpace),
      letI : Fintype (SpectralIndex n) := spectralFintype n
      ∑ i : SpectralIndex n, spectralWeight n x i = ‖x‖ ^ 2
  transferRayleighSpectralRepresentation :
    ∀ (n : ℕ) (x : StateSpace),
      letI : Fintype (SpectralIndex n) := spectralFintype n
      inner ℝ (transferOperator n x) x =
        ∑ i : SpectralIndex n,
          spectralWeight n x i * Real.exp (-spectralEnergy n i)
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
  FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData.stateInnerProductSpace

/-- Finite spectral support above the exact gap generates transfer positivity
and the exact-gap upper Rayleigh estimate. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData.toPositiveRayleighData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W) :
    FiniteWilsonOSAutomaticExactGapPositiveRayleighContractionData W :=
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
    rayleighNonnegative := by
      intro n x
      letI : Fintype (D.SpectralIndex n) := D.spectralFintype n
      rw [D.transferRayleighSpectralRepresentation n x]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (D.spectralWeight_nonneg n x i) (Real.exp_pos _).le
    rayleighUpperBound := by
      intro n x
      letI : Fintype (D.SpectralIndex n) := D.spectralFintype n
      rw [D.transferRayleighSpectralRepresentation n x]
      calc
        ∑ i : D.SpectralIndex n,
            D.spectralWeight n x i * Real.exp (-D.spectralEnergy n i) ≤
          ∑ i : D.SpectralIndex n,
            D.spectralWeight n x i * exactGapClusterContractionRatio := by
              apply Finset.sum_le_sum
              intro i hi
              apply mul_le_mul_of_nonneg_left
              · unfold exactGapClusterContractionRatio
                exact Real.exp_le_exp.mpr
                  (neg_le_neg (D.spectralEnergy_ge_exactGap n i))
              · exact D.spectralWeight_nonneg n x i
        _ = ∑ i : D.SpectralIndex n,
            exactGapClusterContractionRatio * D.spectralWeight n x i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = exactGapClusterContractionRatio *
            ∑ i : D.SpectralIndex n, D.spectralWeight n x i := by
              rw [Finset.mul_sum]
        _ = exactGapClusterContractionRatio * ‖x‖ ^ 2 := by
              rw [D.spectralWeight_sum n x]
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Finite spectral decomposition above the exact gap generates the
transfer-operator norm contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_finite_spectral_data
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_positive_rayleigh
    D.toPositiveRayleighData n

/-- Finite spectral decomposition above the exact gap generates finite-volume
exact-gap connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_finite_spectral_data
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_positive_rayleigh
    D.toPositiveRayleighData n O r

/-- Finite spectral decomposition above the exact gap passes to continuum
clustering after pointwise convergence. -/
theorem finite_wilson_exact_gap_finite_spectral_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W) :
    D.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_positive_rayleigh_passes_to_limit
    D.toPositiveRayleighData

/-- The continuum connected correlation inherits the exact-gap estimate from
the finite spectral support condition. -/
theorem finite_wilson_exact_gap_finite_spectral_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_positive_rayleigh_continuum_bound
    D.toPositiveRayleighData O r

end

end MathlibAnalytic
end MGAP4D
