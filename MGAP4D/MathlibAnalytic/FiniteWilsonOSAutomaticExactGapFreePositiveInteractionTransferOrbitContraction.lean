import MGAP4D.MathlibAnalytic.QuadraticFormLowerBoundPositivePerturbation
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson data in which the Hamiltonian is split into a coercive free
part and a positive interaction.  The total Hamiltonian, its symmetry, its
coercive lower bound, and hence its exact spectral gap are theorem-generated. -/
structure FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData
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
  freeHamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
  interactionHamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
  freeHamiltonianSymmetric :
    ∀ n : ℕ, (freeHamiltonian n).IsSymmetric
  freeHamiltonianQuadraticFormLowerBound :
    ∀ (n : ℕ) (x : StateSpace),
      exactGapValueReal * ‖x‖ ^ 2 ≤
        inner ℝ (freeHamiltonian n x) x
  interactionHamiltonianPositive :
    ∀ n : ℕ, (interactionHamiltonian n).IsPositive
  initialCorrelationState : ℕ → Observable → StateSpace
  correlationReadout : ℕ → Observable → StateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((isSymmetric_add_of_isPositive
                (freeHamiltonianSymmetric n)
                (interactionHamiltonianPositive n)).eigenvectorBasis stateFinrank)
              (fun i =>
                Real.exp
                  (-((isSymmetric_add_of_isPositive
                    (freeHamiltonianSymmetric n)
                    (interactionHamiltonianPositive n)).eigenvalues stateFinrank i))))
            (initialCorrelationState n O) r)
  readoutInitialStateBound :
    ∀ (n : ℕ) (O : Observable),
      ‖correlationReadout n O‖ * ‖initialCorrelationState n O‖ ≤
        decayAmplitude O
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))

attribute [instance]
  FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData.stateFiniteDimensional

/-- The total finite-volume Hamiltonian. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData.hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (n : ℕ) : D.StateSpace →ₗ[ℝ] D.StateSpace :=
  D.freeHamiltonian n + D.interactionHamiltonian n

/-- Positivity of the interaction preserves symmetry of the total Hamiltonian. -/
theorem finite_wilson_free_positive_total_hamiltonian_symmetric
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (n : ℕ) :
    (D.hamiltonian n).IsSymmetric :=
  isSymmetric_add_of_isPositive
    (D.freeHamiltonianSymmetric n)
    (D.interactionHamiltonianPositive n)

/-- Positivity of the interaction preserves the exact quadratic-form lower
bound of the free Hamiltonian. -/
theorem finite_wilson_free_positive_total_hamiltonian_coercive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (D.hamiltonian n x) x :=
  quadratic_form_lower_bound_add_of_isPositive
    exactGapValueReal
    (D.freeHamiltonianQuadraticFormLowerBound n)
    (D.interactionHamiltonianPositive n)
    x

/-- Enter the coercive route only after constructing the total Hamiltonian and
proving its lower bound from the free-plus-positive-interaction split. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData.toCoerciveTransferOrbitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W :=
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
    hamiltonian := D.hamiltonian
    hamiltonianSymmetric :=
      finite_wilson_free_positive_total_hamiltonian_symmetric D
    hamiltonianQuadraticFormLowerBound :=
      finite_wilson_free_positive_total_hamiltonian_coercive D
    initialCorrelationState := D.initialCorrelationState
    correlationReadout := D.correlationReadout
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- The total Hamiltonian eigenvalues inherit the exact lower bound from the
coercive free part and positive interaction. -/
theorem finite_wilson_free_positive_hamiltonian_eigenvalues_ge_exactGap
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (finite_wilson_free_positive_total_hamiltonian_symmetric D n).eigenvalues
        D.stateFinrank i :=
  finite_wilson_coercive_hamiltonian_eigenvalues_ge_exactGap
    D.toCoerciveTransferOrbitData n i

/-- The free-plus-positive-interaction decomposition generates finite-volume
exact-gap connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_free_positive_interaction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_coercive_hamiltonian
    D.toCoerciveTransferOrbitData n O r

/-- The free-plus-positive-interaction gap passes to continuum clustering after
pointwise convergence. -/
theorem finite_wilson_exact_gap_free_positive_interaction_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W) :
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.toConstructedHamiltonianTransferData.toHamiltonianEigenactionData.toFiniteDimensionalHamiltonianData.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_coercive_hamiltonian_passes_to_limit
    D.toCoerciveTransferOrbitData

/-- The continuum connected correlation inherits the public exact-gap estimate
from the free coercive part plus positive interaction. -/
theorem finite_wilson_exact_gap_free_positive_interaction_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_coercive_hamiltonian_continuum_bound
    D.toCoerciveTransferOrbitData O r

end

end MathlibAnalytic
end MGAP4D
