import MGAP4D.MathlibAnalytic.OrthonormalEigenactionRayleigh
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite-volume Wilson transfer data in which the transfer operator acts as
`exp (-E)` on the orthonormal eigenbasis generated from a finite-dimensional
symmetric Hamiltonian.

Unlike `FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData`,
the Rayleigh spectral expansion is not an input field.  It is derived from
transfer symmetry, the generated orthonormal basis, and the eigenaction. -/
structure FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData
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
  transferOnHamiltonianEigenbasis :
    ∀ (n : ℕ) (i : Fin StateDimension),
      transferOperator n
          ((hamiltonianSymmetric n).eigenvectorBasis stateFinrank i) =
        Real.exp (-((hamiltonianSymmetric n).eigenvalues stateFinrank i)) •
          ((hamiltonianSymmetric n).eigenvectorBasis stateFinrank i)
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
  FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData.stateFiniteDimensional

/-- The transfer Rayleigh expansion follows from the Hamiltonian eigenaction;
it is no longer an independent analytic input. -/
theorem finite_wilson_hamiltonian_eigenaction_rayleigh_representation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W)
    (n : ℕ) (x : D.StateSpace) :
    inner ℝ (D.transferOperator n x) x =
      ∑ i : Fin D.StateDimension,
        (inner ℝ
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank i) x) ^ 2 *
          Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) := by
  exact rayleigh_eq_sum_of_orthonormal_eigenaction
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    (D.transferOperator n)
    (fun i =>
      Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))
    (D.transferSymmetric n)
    (D.transferOnHamiltonianEigenbasis n)
    x

/-- Forget the eigenaction presentation only after the Rayleigh expansion has
been theorem-generated. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData.toFiniteDimensionalHamiltonianData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W) :
    FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W :=
  { Observable := D.Observable
    StateSpace := D.StateSpace
    stateNormedAddCommGroup := D.stateNormedAddCommGroup
    stateInnerProductSpace := D.stateInnerProductSpace
    stateFiniteDimensional := D.stateFiniteDimensional
    StateDimension := D.StateDimension
    stateFinrank := D.stateFinrank
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    decayAmplitude_nonneg := D.decayAmplitude_nonneg
    hamiltonian := D.hamiltonian
    hamiltonianSymmetric := D.hamiltonianSymmetric
    hamiltonianEigenvalues_ge_exactGap := D.hamiltonianEigenvalues_ge_exactGap
    transferOperator := D.transferOperator
    transferSymmetric := D.transferSymmetric
    transferRayleighHamiltonianEigenbasisRepresentation :=
      finite_wilson_hamiltonian_eigenaction_rayleigh_representation D
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := D.state_succ
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Hamiltonian eigenaction above the exact gap generates the one-step transfer
operator contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_hamiltonian_eigenaction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W)
    (n : ℕ) :
    ‖D.transferOperator n‖ ≤ exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_finite_dimensional_hamiltonian
    D.toFiniteDimensionalHamiltonianData n

/-- Hamiltonian eigenaction above the exact gap generates the finite-volume
connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_hamiltonian_eigenaction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_finite_dimensional_hamiltonian
    D.toFiniteDimensionalHamiltonianData n O r

/-- Hamiltonian eigenaction exact-gap control passes to continuum clustering
after pointwise convergence. -/
theorem finite_wilson_exact_gap_hamiltonian_eigenaction_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W) :
    D.toFiniteDimensionalHamiltonianData.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_finite_dimensional_hamiltonian_passes_to_limit
    D.toFiniteDimensionalHamiltonianData

/-- The continuum connected correlation inherits the exact-gap estimate from
the Hamiltonian eigenaction. -/
theorem finite_wilson_exact_gap_hamiltonian_eigenaction_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapHamiltonianEigenactionContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_finite_dimensional_hamiltonian_continuum_bound
    D.toFiniteDimensionalHamiltonianData O r

end

end MathlibAnalytic
end MGAP4D
