import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperatorLowerBound
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson data where the free Hamiltonian is constructed diagonally
from explicit orthonormal modes and mode energies, while the interaction is
positive.  The free coercive estimate is generated from the pointwise mode
energy lower bound. -/
structure FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData
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
  freeEigenbasis :
    ℕ → OrthonormalBasis (Fin StateDimension) ℝ StateSpace
  freeModeEnergy : ℕ → Fin StateDimension → ℝ
  freeModeEnergy_ge_exactGap :
    ∀ (n : ℕ) (i : Fin StateDimension),
      exactGapValueReal ≤ freeModeEnergy n i
  interactionHamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
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
                (orthonormalDiagonalLinearMap_isSymmetric
                  (freeEigenbasis n) (freeModeEnergy n))
                (interactionHamiltonianPositive n)).eigenvectorBasis stateFinrank)
              (fun i =>
                Real.exp
                  (-((isSymmetric_add_of_isPositive
                    (orthonormalDiagonalLinearMap_isSymmetric
                      (freeEigenbasis n) (freeModeEnergy n))
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
  FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData.stateFiniteDimensional

/-- The free Hamiltonian constructed from its explicit orthonormal modes. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData.freeHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (n : ℕ) : D.StateSpace →ₗ[ℝ] D.StateSpace :=
  (orthonormalDiagonalOperator (D.freeEigenbasis n) (D.freeModeEnergy n)).toLinearMap

/-- The mode-energy lower bound generates the basis-free free-Hamiltonian
coercive estimate. -/
theorem finite_wilson_mode_diagonal_free_hamiltonian_coercive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (n : ℕ) (x : D.StateSpace) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ (D.freeHamiltonian n x) x :=
  orthonormalDiagonalOperator_quadratic_form_lower_bound
    (D.freeEigenbasis n)
    (D.freeModeEnergy n)
    exactGapValueReal
    (D.freeModeEnergy_ge_exactGap n)
    x

/-- The mode-diagonal free Hamiltonian is symmetric. -/
theorem finite_wilson_mode_diagonal_free_hamiltonian_symmetric
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (n : ℕ) :
    (D.freeHamiltonian n).IsSymmetric :=
  orthonormalDiagonalLinearMap_isSymmetric
    (D.freeEigenbasis n) (D.freeModeEnergy n)

/-- Convert to the free-plus-positive-interaction route only after deriving the
free coercive estimate from the explicit mode energies. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData.toFreePositiveInteractionData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W) :
    FiniteWilsonOSAutomaticExactGapFreePositiveInteractionTransferOrbitContractionData W :=
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
    freeHamiltonian := D.freeHamiltonian
    interactionHamiltonian := D.interactionHamiltonian
    freeHamiltonianSymmetric :=
      finite_wilson_mode_diagonal_free_hamiltonian_symmetric D
    freeHamiltonianQuadraticFormLowerBound :=
      finite_wilson_mode_diagonal_free_hamiltonian_coercive D
    interactionHamiltonianPositive := D.interactionHamiltonianPositive
    initialCorrelationState := D.initialCorrelationState
    correlationReadout := D.correlationReadout
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Explicit mode-energy bounds generate the exact total-Hamiltonian spectral
lower bound in the presence of a positive interaction. -/
theorem finite_wilson_mode_diagonal_total_hamiltonian_eigenvalues_ge_exactGap
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (finite_wilson_free_positive_total_hamiltonian_symmetric
        D.toFreePositiveInteractionData n).eigenvalues D.stateFinrank i :=
  finite_wilson_free_positive_hamiltonian_eigenvalues_ge_exactGap
    D.toFreePositiveInteractionData n i

/-- Mode-energy lower bounds and positive interaction generate finite-volume
exact-gap connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_mode_diagonal_free_positive_interaction
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_free_positive_interaction
    D.toFreePositiveInteractionData n O r

/-- The continuum connected correlation inherits the exact-gap estimate from
explicit free mode-energy bounds and positivity of the interaction. -/
theorem finite_wilson_exact_gap_mode_diagonal_free_positive_interaction_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapModeDiagonalFreePositiveInteractionContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_free_positive_interaction_continuum_bound
    D.toFreePositiveInteractionData O r

end

end MathlibAnalytic
end MGAP4D
