import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumLocalPoincareTensorizationGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite Wilson transfer-orbit data whose spectral gap is generated from
local conditional-variance tensorization and local Poincare inequalities. -/
structure FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  gapData : FiniteWilsonVacuumLocalPoincareTensorizationGapData
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  initialCorrelationState :
    ℕ → Observable →
      gapData.toVacuumPoincareGapData.toDerivedInvarianceGapData.ExcitedStateSpace
  correlationReadout :
    ℕ → Observable →
      gapData.toVacuumPoincareGapData.toDerivedInvarianceGapData.ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                gapData.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvectorBasis
                  gapData.excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    gapData.toVacuumPoincareGapData.toDerivedInvarianceGapData.toVacuumOrthogonalGapData n).eigenvalues
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

/-- Enter the vacuum-Poincare transfer route after generating its global
Poincare inequality from local update estimates. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData.toVacuumPoincareData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData W) :
    FiniteWilsonOSAutomaticExactGapVacuumPoincareTransferOrbitContractionData W :=
  { Observable := D.Observable
    gapData := D.gapData.toVacuumPoincareGapData
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

/-- Local update Poincare estimates generate finite-volume exact-gap
connected-correlation decay. -/
theorem finite_wilson_exact_gap_bound_of_local_poincare_tensorization
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_vacuum_poincare
    D.toVacuumPoincareData n O r

/-- The continuum connected correlation inherits the exact-gap estimate from
the local update Poincare and tensorization data. -/
theorem finite_wilson_exact_gap_local_poincare_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapLocalPoincareTransferOrbitContractionData W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_poincare_continuum_bound
    D.toVacuumPoincareData O r

end

end MathlibAnalytic
end MGAP4D
