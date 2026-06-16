import MGAP4D.MathlibAnalytic.FiniteWilsonSingleLinkHeatBathHamiltonianBridge
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson transfer-orbit data whose spectral gap is generated from the
concrete single-link heat-bath Poincare inequality and a Hilbert-observable
realization bridge. -/
structure FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  bridgeData : FiniteWilsonSingleLinkHeatBathHamiltonianBridgeData W
  leftObservable :
    (n : ℕ) → Observable →
      (W.system (bridgeData.scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ →
      (W.system (bridgeData.scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  initialCorrelationState :
    ℕ → Observable →
      bridgeData.toVacuumPoincareGapData.toDerivedInvarianceGapData.ExcitedStateSpace
  correlationReadout :
    ℕ → Observable →
      bridgeData.toVacuumPoincareGapData.toDerivedInvarianceGapData.ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (bridgeData.scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                bridgeData.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvectorBasis
                  bridgeData.excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    bridgeData.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
                      bridgeData.excitedFinrank i))))
            (initialCorrelationState n O) r)
  readoutInitialStateBound :
    ∀ (n : ℕ) (O : Observable),
      ‖correlationReadout n O‖ * ‖initialCorrelationState n O‖ ≤
        decayAmplitude O
  pointwiseConvergence :
    ∀ (O : Observable) (r : ℕ),
      Tendsto
        (fun n : ℕ =>
          (W.system (bridgeData.scale n)).gibbsConnectedCorrelation
            (leftObservable n O) (rightObservable n O r))
        atTop (nhds (continuumConnectedCorrelation O r))

/-- Enter the vacuum-Poincare transfer route after deriving the global gap from
the concrete single-link Wilson heat-bath form. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData.toVacuumPoincareData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W :=
  { Observable := D.Observable
    gapData := D.bridgeData.toVacuumPoincareGapData
    scale := D.bridgeData.scale
    leftObservable := D.leftObservable
    rightObservable := D.rightObservable
    continuumConnectedCorrelation := D.continuumConnectedCorrelation
    decayAmplitude := D.decayAmplitude
    initialCorrelationState := D.initialCorrelationState
    correlationReadout := D.correlationReadout
    connectedCorrelation_representation := D.connectedCorrelation_representation
    readoutInitialStateBound := D.readoutInitialStateBound
    pointwiseConvergence := D.pointwiseConvergence }

/-- The concrete heat-bath Poincare estimate generates finite-volume exact-gap
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_single_link_heat_bath
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.bridgeData.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_vacuum_poincare
    D.toVacuumPoincareData n O r

/-- The continuum connected correlation inherits the exact-gap estimate from
the concrete single-link heat-bath Poincare inequality. -/
theorem finite_wilson_exact_gap_single_link_heat_bath_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapSingleLinkHeatBathTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_poincare_continuum_bound
    D.toVacuumPoincareData O r

end

end MathlibAnalytic
end MGAP4D
