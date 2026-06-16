import Mathlib.Analysis.InnerProductSpace.Spectrum
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite-volume transfer data controlled by a finite-dimensional symmetric
Hamiltonian.  Mathlib's finite-dimensional spectral theorem generates the
orthonormal eigenbasis and ordered real eigenvalues. -/
structure FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  StateSpace : Type
  [stateNormedAddCommGroup : NormedAddCommGroup StateSpace]
  [stateInnerProductSpace : InnerProductSpace ℝ StateSpace]
  [stateFiniteDimensional : FiniteDimensional ℝ StateSpace]
  StateDimension : ℕ
  stateFinrank : Module.finrank ℝ StateSpace = StateDimension
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  decayAmplitude_nonneg : ∀ O : Observable, 0 ≤ decayAmplitude O
  hamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
  hamiltonianSymmetric :
    ∀ n : ℕ, (hamiltonian n).IsSymmetric
  hamiltonianEigenvalues_ge_exactGap :
    ∀ (n : ℕ) (i : Fin StateDimension),
      exactGapValueReal ≤
        (hamiltonianSymmetric n).eigenvalues stateFinrank i
  transferOperator : ℕ → StateSpace →L[ℝ] StateSpace
  transferSymmetric :
    ∀ (n : ℕ) (x y : StateSpace),
      inner ℝ (transferOperator n x) y =
        inner ℝ (transferOperator n y) x
  transferRayleighHamiltonianEigenbasisRepresentation :
    ∀ (n : ℕ) (x : StateSpace),
      inner ℝ (transferOperator n x) x =
        ∑ i : Fin StateDimension,
          (inner ℝ
            ((hamiltonianSymmetric n).eigenvectorBasis stateFinrank i) x) ^ 2 *
            Real.exp (-((hamiltonianSymmetric n).eigenvalues stateFinrank i))
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
  FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData.stateFiniteDimensional

/-- A finite-dimensional symmetric Hamiltonian generates the orthonormal
Hamiltonian-eigenbasis transfer package. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData.toOrthonormalEigenbasisData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W) :
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
    transferSymmetric := D.transferSymmetric
    SpectralIndex := fun _ => Fin D.StateDimension
    spectralFintype := fun _ => inferInstance
    spectralBasis := fun n =>
      (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank
    spectralEnergy := fun n =>
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank
    spectralEnergy_ge_exactGap := D.hamiltonianEigenvalues_ge_exactGap
    transferRayleighEigenbasisRepresentation :=
      D.transferRayleighHamiltonianEigenbasisRepresentation
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- The generated Hamiltonian eigenbasis is a genuine orthonormal basis of the
finite transfer-state sector. -/
theorem finite_wilson_finite_dimensional_hamiltonian_eigenbasis_orthonormal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ) :
    Orthonormal ℝ
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank) :=
  ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank).orthonormal

/-- Every generated basis vector is an eigenvector of the finite-dimensional
Hamiltonian with the corresponding generated real eigenvalue. -/
theorem finite_wilson_finite_dimensional_hamiltonian_apply_eigenbasis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ) (i : Fin D.StateDimension) :
    D.hamiltonian n
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) =
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i •
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) :=
  (D.hamiltonianSymmetric n).apply_eigenvectorBasis D.stateFinrank i

/-- A finite-dimensional symmetric Hamiltonian whose generated eigenvalues lie
above the public exact gap yields transfer contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_finite_dimensional_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_orthonormal_eigenbasis
    D.toOrthonormalEigenbasisData n

/-- The finite-dimensional Hamiltonian spectral gap generates finite-volume
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_finite_dimensional_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_orthonormal_eigenbasis
    D.toOrthonormalEigenbasisData n O r

/-- The finite-dimensional Hamiltonian exact gap passes to continuum
clustering after pointwise convergence. -/
theorem finite_wilson_exact_gap_finite_dimensional_hamiltonian_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W) :
    D.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_orthonormal_eigenbasis_passes_to_limit
    D.toOrthonormalEigenbasisData

/-- The continuum connected correlation inherits the exact-gap estimate from
the finite-dimensional Hamiltonian spectrum. -/
theorem finite_wilson_exact_gap_finite_dimensional_hamiltonian_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_orthonormal_eigenbasis_continuum_bound
    D.toOrthonormalEigenbasisData O r

end

end MathlibAnalytic
end MGAP4D
