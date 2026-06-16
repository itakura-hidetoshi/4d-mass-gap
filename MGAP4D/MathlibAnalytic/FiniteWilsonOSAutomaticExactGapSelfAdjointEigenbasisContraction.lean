import Mathlib.Analysis.InnerProductSpace.Spectrum
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

structure FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateInnerProductSpace : InnerProductSpace ℝ StateSpace]
  [stateFiniteDimensional : FiniteDimensional ℝ StateSpace]
  stateDimension : ℕ
  stateFinrank : Module.finrank ℝ StateSpace = stateDimension
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  decayAmplitude_nonneg : ∀ O : Observable, 0 ≤ decayAmplitude O
  transferOperator : ℕ → StateSpace →L[ℝ] StateSpace
  transferLinearSymmetric :
    ∀ n : ℕ, (transferOperator n).toLinearMap.IsSymmetric
  spectralEnergy : ℕ → Fin stateDimension → ℝ
  spectralEnergy_ge_exactGap :
    ∀ (n : ℕ) (i : Fin stateDimension),
      exactGapValueReal ≤ spectralEnergy n i
  transferEigenvalue_eq_exp_neg_energy :
    ∀ (n : ℕ) (i : Fin stateDimension),
      (transferLinearSymmetric n).eigenvalues stateFinrank i =
        Real.exp (-spectralEnergy n i)
  transferRayleighEigenbasisRepresentation :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (transferOperator n x) x =
        ∑ i : Fin stateDimension,
          (inner ℝ
              ((transferLinearSymmetric n).eigenvectorBasis stateFinrank i)
              x) ^ 2 * Real.exp (-spectralEnergy n i)
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
  FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.stateFiniteDimensional

noncomputable def
    FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.generatedSpectralBasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W)
    (n : ℕ) : OrthonormalBasis (Fin D.stateDimension) ℝ D.StateSpace :=
  (D.transferLinearSymmetric n).eigenvectorBasis D.stateFinrank

theorem finite_wilson_generated_spectral_basis_hasEigenvector
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W)
    (n : ℕ) (i : Fin D.stateDimension) :
    HasEigenvector (D.transferOperator n).toLinearMap
      ((D.transferLinearSymmetric n).eigenvalues D.stateFinrank i)
      (D.generatedSpectralBasis n i) := by
  simpa [FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.generatedSpectralBasis]
    using (D.transferLinearSymmetric n).hasEigenvector_eigenvectorBasis
      D.stateFinrank i

noncomputable def
    FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.toOrthonormalEigenbasisData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W) :
    FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContractionData W :=
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
    transferSymmetric := by
      intro n x y
      calc
        inner ℝ (D.transferOperator n x) y =
            inner ℝ x (D.transferOperator n y) :=
          D.transferLinearSymmetric n x y
        _ = inner ℝ (D.transferOperator n y) x := real_inner_comm _ _
    SpectralIndex := fun _ => Fin D.stateDimension
    spectralFintype := fun _ => inferInstance
    spectralBasis := fun n => D.generatedSpectralBasis n
    spectralEnergy := D.spectralEnergy
    spectralEnergy_ge_exactGap := D.spectralEnergy_ge_exactGap
    transferRayleighEigenbasisRepresentation := by
      intro n x
      simpa [FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.generatedSpectralBasis]
        using D.transferRayleighEigenbasisRepresentation n x
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

noncomputable def
    FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData.toFiniteSpectralData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W) :
    FiniteWilsonOSAutomaticExactGapFiniteSpectralContractionData W :=
  D.toOrthonormalEigenbasisData.toFiniteSpectralData

theorem finite_wilson_exact_gap_operator_norm_bound_of_self_adjoint_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_orthonormal_eigenbasis
    D.toOrthonormalEigenbasisData n

theorem finite_wilson_exact_gap_self_adjoint_eigenbasis_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSelfAdjointEigenbasisContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_orthonormal_eigenbasis_continuum_bound
    D.toOrthonormalEigenbasisData O r

end

end MathlibAnalytic
end MGAP4D
