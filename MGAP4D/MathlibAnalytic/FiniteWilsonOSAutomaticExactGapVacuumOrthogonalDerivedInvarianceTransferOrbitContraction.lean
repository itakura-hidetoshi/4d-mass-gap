import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumOrthogonalDerivedInvarianceGap

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson transfer-orbit data in which vacuum-orthogonal invariance is
not supplied.  It is generated from Hamiltonian symmetry and `H Ω = 0`. -/
structure FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  gapData : FiniteWilsonVacuumOrthogonalDerivedInvarianceGapData
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  initialCorrelationState :
    ℕ → Observable → gapData.ExcitedStateSpace
  correlationReadout :
    ℕ → Observable → gapData.ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                gapData.toVacuumOrthogonalGapData n).eigenvectorBasis
                  gapData.excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    gapData.toVacuumOrthogonalGapData n).eigenvalues
                      gapData.excitedFinrank i))))
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

/-- Enter the established vacuum-orthogonal route after the sector-invariance
field has been discharged. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData.toVacuumOrthogonalData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W :=
  { Observable := D.Observable
    gapData := D.gapData.toVacuumOrthogonalGapData
    scale := D.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    initialCorrelationState := D.initialCorrelationState
    correlationReadout := D.correlationReadout
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- Derived sector invariance yields finite-volume exact-gap correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_vacuum_orthogonal_derived_invariance
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_vacuum_orthogonal_coercive_hamiltonian
    D.toVacuumOrthogonalData n O r

/-- The continuum correlation inherits the exact-gap estimate after deriving
vacuum-sector invariance from symmetry and zero vacuum energy. -/
theorem finite_wilson_exact_gap_vacuum_orthogonal_derived_invariance_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_coercive_continuum_bound
    D.toVacuumOrthogonalData O r

end

end MathlibAnalytic
end MGAP4D
