import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- The forward orbit of an initial vector under a continuous linear
endomorphism. -/
def continuousLinearMapOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | Nat.succ r => T (continuousLinearMapOrbit T x₀ r)

@[simp]
theorem continuousLinearMapOrbit_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (x₀ : E) :
    continuousLinearMapOrbit T x₀ 0 = x₀ := rfl

@[simp]
theorem continuousLinearMapOrbit_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E) (x₀ : E) (r : ℕ) :
    continuousLinearMapOrbit T x₀ (Nat.succ r) =
      T (continuousLinearMapOrbit T x₀ r) := rfl

/-- Finite Wilson Hamiltonian data in which both the transfer operator and the
entire correlation-state sequence are constructed.  Only the initial state is
supplied; later states are its forward transfer orbit. -/
structure FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData
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
  hamiltonianEigenvalues_ge_exactGap :
    ∀ (n : ℕ) (i : Fin StateDimension),
      exactGapValueReal ≤
        (hamiltonianSymmetric n).eigenvalues stateFinrank i
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
  FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.stateNormedAddCommGroup
  FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.stateInnerProductSpace
  FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.stateFiniteDimensional

/-- The volume-uniform initial-state estimate forces the decay amplitude to be
nonnegative; this sign condition is not an independent input. -/
theorem finite_wilson_constructed_transfer_orbit_decayAmplitude_nonneg
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (O : D.Observable) :
    0 ≤ D.decayAmplitude O := by
  calc
    0 ≤ ‖D.correlationReadout 0 O‖ * ‖D.initialCorrelationState 0 O‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ ≤ D.decayAmplitude O := D.readoutInitialStateBound 0 O

/-- The canonically constructed Hamiltonian transfer operator. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.transferOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) : D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalOperator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    (fun i =>
      Real.exp (-((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)))

/-- The correlation-state sequence constructed as a transfer orbit. -/
def FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.correlationState
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) : D.StateSpace :=
  continuousLinearMapOrbit (D.transferOperator n)
    (D.initialCorrelationState n O) r

@[simp]
theorem finite_wilson_constructed_transfer_orbit_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) :
    D.correlationState n O 0 = D.initialCorrelationState n O := rfl

@[simp]
theorem finite_wilson_constructed_transfer_orbit_succ
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    D.correlationState n O (Nat.succ r) =
      D.transferOperator n (D.correlationState n O r) := rfl

/-- Enter the existing constructed-Hamiltonian-transfer route only after the
full correlation-state sequence and its recurrence have been generated. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.toConstructedHamiltonianTransferData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapConstructedHamiltonianTransferContractionData W :=
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
    decayAmplitude_nonneg :=
      finite_wilson_constructed_transfer_orbit_decayAmplitude_nonneg D
    hamiltonian := D.hamiltonian
    hamiltonianSymmetric := D.hamiltonianSymmetric
    hamiltonianEigenvalues_ge_exactGap := D.hamiltonianEigenvalues_ge_exactGap
    correlationState := D.correlationState
    correlationReadout := D.correlationReadout
    state_succ := finite_wilson_constructed_transfer_orbit_succ D
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := by
      intro n O
      simpa using D.readoutInitialStateBound n O
    pointwiseConvergence := D.pointwiseConvergence }

/-- The constructed transfer orbit satisfies finite-volume exact-gap decay. -/
theorem finite_wilson_exact_gap_bound_of_constructed_transfer_orbit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_constructed_hamiltonian_transfer
    D.toConstructedHamiltonianTransferData n O r

/-- The transfer-orbit construction passes to continuum clustering after
pointwise convergence. -/
theorem finite_wilson_exact_gap_constructed_transfer_orbit_passes_to_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W) :
    D.toConstructedHamiltonianTransferData.toHamiltonianEigenactionData.toFiniteDimensionalHamiltonianData.toOrthonormalEigenbasisData.toFiniteSpectralData.toPositiveRayleighData.toSymmetricRayleighData.toHilbertMatrixData.toTransferOperatorData.toExactGapClusterData.toUniformGeometricClusterData.toClusterLimitData.toClusterLimitData.ContinuumClusterProperty :=
  finite_wilson_exact_gap_constructed_hamiltonian_transfer_passes_to_limit
    D.toConstructedHamiltonianTransferData

/-- The continuum connected correlation inherits the exact-gap estimate from
the constructed transfer orbit. -/
theorem finite_wilson_exact_gap_constructed_transfer_orbit_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_constructed_hamiltonian_transfer_continuum_bound
    D.toConstructedHamiltonianTransferData O r

end

end MathlibAnalytic
end MGAP4D
