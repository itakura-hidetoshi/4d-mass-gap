import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson transfer-orbit data whose spectral gap is generated from a
vacuum-centered Poincare inequality and a Dirichlet-form representation. -/
structure FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  gapData : FiniteWilsonVacuumPoincareHamiltonianGapData
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  initialCorrelationState :
    ℕ → Observable → gapData.toDerivedInvarianceGapData.ExcitedStateSpace
  correlationReadout :
    ℕ → Observable →
      gapData.toDerivedInvarianceGapData.ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                gapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvectorBasis
                  gapData.excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    gapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
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

/-- Enter the derived vacuum-invariance route after generating coercivity from
the Poincare inequality. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData.toDerivedInvarianceData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData W :=
  { Observable := D.Observable
    gapData := D.gapData.toDerivedInvarianceGapData
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

/-- The vacuum Poincare inequality generates finite-volume exact-gap
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_vacuum_poincare
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_vacuum_orthogonal_derived_invariance
    D.toDerivedInvarianceData n O r

/-- The continuum correlation inherits the exact-gap estimate from the
vacuum-centered Poincare inequality. -/
theorem finite_wilson_exact_gap_vacuum_poincare_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_derived_invariance_continuum_bound
    D.toDerivedInvarianceData O r

end

end MathlibAnalytic
end MGAP4D
