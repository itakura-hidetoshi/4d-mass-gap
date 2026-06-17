import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalDobrushinScaledHamiltonianFamilyGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Transfer-orbit data whose exact finite-dimensional gap is generated
canonically from strict Dobrushin matrix data.

The Dobrushin argument discharges the Hamiltonian-gap field.  The representation
of correlations on the selected excitation space, together with cross-scale
convergence, remains an explicit independent input. -/
structure
    FiniteWilsonOSAutomaticExactGapCanonicalDobrushinScaledTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  dobrushinData : FiniteWilsonCanonicalDobrushinMatrixFamilyData W
  gapScale : W.index
  scale : ℕ → W.index
  leftObservable :
    (n : ℕ) → Observable → (W.system (scale n)).Configuration → ℝ
  rightObservable :
    (n : ℕ) → Observable → ℕ → (W.system (scale n)).Configuration → ℝ
  continuumConnectedCorrelation : Observable → ℕ → ℝ
  decayAmplitude : Observable → ℝ
  initialCorrelationState :
    ℕ → Observable →
      (dobrushinData.hamiltonianGapData gapScale).ExcitedStateSpace
  correlationReadout :
    ℕ → Observable →
      (dobrushinData.hamiltonianGapData gapScale).ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                (dobrushinData.hamiltonianGapData gapScale).toVacuumOrthogonalGapData
                n).eigenvectorBasis
                  (dobrushinData.hamiltonianGapData gapScale).excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    (dobrushinData.hamiltonianGapData gapScale).toVacuumOrthogonalGapData
                    n).eigenvalues
                      (dobrushinData.hamiltonianGapData gapScale).excitedFinrank i))))
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

/-- Forget only the canonical Dobrushin origin of the gap and enter the generic
derived-invariance transfer-orbit theorem. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapCanonicalDobrushinScaledTransferOrbitContractionData.toDerivedInvarianceData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapCanonicalDobrushinScaledTransferOrbitContractionData
        W) :
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalDerivedInvarianceTransferOrbitContractionData
      W :=
  { Observable := D.Observable
    gapData := D.dobrushinData.hamiltonianGapData D.gapScale
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

/-- Canonically generated Dobrushin Hamiltonian gaps imply the finite-scale
transfer-orbit connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_canonical_dobrushin_scaled_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapCanonicalDobrushinScaledTransferOrbitContractionData
        W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_vacuum_orthogonal_derived_invariance
    D.toDerivedInvarianceData n O r

/-- Under the explicit correlation representation and pointwise convergence
assumptions, the continuum connected correlation inherits the exact-gap decay
from the canonically generated Dobrushin Hamiltonian. -/
theorem finite_wilson_exact_gap_canonical_dobrushin_scaled_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapCanonicalDobrushinScaledTransferOrbitContractionData
        W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_vacuum_orthogonal_derived_invariance_continuum_bound
    D.toDerivedInvarianceData O r

end

end MathlibAnalytic
end MGAP4D
