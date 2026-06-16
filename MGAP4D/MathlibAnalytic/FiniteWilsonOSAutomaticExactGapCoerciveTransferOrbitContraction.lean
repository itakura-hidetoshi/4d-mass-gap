import MGAP4D.MathlibAnalytic.SymmetricEigenvalueLowerBound
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson Hamiltonian data where the exact spectral gap is not supplied
as an eigenvalue inequality.  Instead one supplies the stronger, basis-free
quadratic-form coercive estimate

`exactGapValueReal * ‖x‖² ≤ ⟪Hₙ x, x⟫`

uniformly in the finite-volume index.  The eigenvalue lower bound is then
proved from mathlib's orthonormal eigenbasis. -/
structure FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData
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
  hamiltonian : ℕ → StateSpace →ₗ[ℝ] StateSpace
  hamiltonianSymmetric :
    ∀ n : ℕ, (hamiltonian n).IsSymmetric
  hamiltonianQuadraticFormLowerBound :
    ∀ (n : ℕ) (x : StateSpace),
      exactGapValueReal * ‖x‖ ^ 2 ≤
        inner ℝ (hamiltonian n x) x
  initialCorrelationState : ℕ → Observable → StateSpace
  correlationReadout : ℕ → Observable → StateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((hamiltonianSymmetric n).eigenvectorBasis stateFinrank)
              (fun i =>
                Real.exp
                  (-((hamiltonianSymmetric n).eigenvalues stateFinrank i))))
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
  FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData.stateFiniteDimensional

/-- Coercivity forces every generated finite-volume Hamiltonian eigenvalue to
lie above the public exact gap. -/
theorem finite_wilson_coercive_hamiltonian_eigenvalues_ge_exactGap
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W)
    (n : ℕ) (i : Fin D.StateDimension) :
    exactGapValueReal ≤
      (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i :=
  symmetric_eigenvalue_ge_of_quadratic_form_lower_bound
    (D.hamiltonianSymmetric n)
    D.stateFinrank
    exactGapValueReal
    (D.hamiltonianQuadraticFormLowerBound n)
    i

/-- Enter the constructed-transfer-orbit route only after the Hamiltonian
spectral lower bound has been theorem-generated from coercivity. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData.toConstructedTransferOrbitData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W :=
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
    hamiltonianSymmetric := D.hamiltonianSymmetric
    hamiltonianEigenvalues_ge_exactGap :=
      finite_wilson_coercive_hamiltonian_eigenvalues_ge_exactGap D
    initialCorrelationState := D.initialCorrelationState
    correlationReadout := D.correlationReadout
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- The canonically constructed transfer operator associated with the coercive
Hamiltonian satisfies the exact-gap operator-norm contraction. -/
theorem finite_wilson_exact_gap_operator_norm_bound_of_coercive_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ‖D.toConstructedTransferOrbitData.transferOperator n‖ ≤
      exactGapClusterContractionRatio :=
  finite_wilson_exact_gap_operator_norm_bound_of_constructed_hamiltonian_transfer
    D.toConstructedTransferOrbitData.toConstructedHamiltonianTransferData n

/-- The coercive Hamiltonian estimate generates finite-volume exact-gap
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_coercive_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_constructed_transfer_orbit
    D.toConstructedTransferOrbitData n O r

/-- Coercive finite-volume Hamiltonian control passes to continuum clustering
after pointwise convergence. -/
theorem finite_wilson_exact_gap_coercive_hamiltonian_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W) :
    D.toConstructedTransferOrbitData.toConstructedHamiltonianTransferData.toHamiltonianEigenactionData.toFiniteDimensionalHamiltonianData.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_constructed_transfer_orbit_passes_to_limit
    D.toConstructedTransferOrbitData

/-- The continuum connected correlation inherits the public exact-gap estimate
from the basis-free coercive Hamiltonian inequality. -/
theorem finite_wilson_exact_gap_coercive_hamiltonian_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapCoerciveTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_constructed_transfer_orbit_continuum_bound
    D.toConstructedTransferOrbitData O r

end

end MathlibAnalytic
end MGAP4D
