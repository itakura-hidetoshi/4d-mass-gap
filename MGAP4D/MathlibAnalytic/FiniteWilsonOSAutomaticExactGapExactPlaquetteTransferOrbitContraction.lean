import MGAP4D.MathlibAnalytic.FiniteWilsonExactPlaquetteDobrushinFamilyGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapCanonicalDobrushinStrictTransferOrbitContraction

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Transfer-orbit data whose finite-volume Hamiltonian gap is generated from
the exact plaquette degree-times-local-influence inequality at every Wilson
scale.

The finite Wilson locality and Dobrushin spectral argument discharge the gap
field.  Correlation representation and continuum convergence remain explicit
independent inputs. -/
structure
    FiniteWilsonOSAutomaticExactGapExactPlaquetteTransferOrbitContractionData
    (W : FiniteWilsonOSAutomaticApproximationFamily) where
  Observable : Type
  profileData : FiniteWilsonExactPlaquetteDobrushinFamilyData W
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
      (profileData.hamiltonianGapData gapScale).ExcitedStateSpace
  correlationReadout :
    ℕ → Observable →
      (profileData.hamiltonianGapData gapScale).ExcitedStateSpace →L[ℝ] ℝ
  connectedCorrelation_representation :
    ∀ (n : ℕ) (O : Observable) (r : ℕ),
      (W.system (scale n)).gibbsConnectedCorrelation
          (leftObservable n O) (rightObservable n O r) =
        correlationReadout n O
          (continuousLinearMapOrbit
            (orthonormalDiagonalOperator
              ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                (profileData.hamiltonianGapData gapScale).toVacuumOrthogonalGapData
                n).eigenvectorBasis
                  (profileData.hamiltonianGapData gapScale).excitedFinrank)
              (fun i =>
                Real.exp
                  (-((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
                    (profileData.hamiltonianGapData gapScale).toVacuumOrthogonalGapData
                    n).eigenvalues
                      (profileData.hamiltonianGapData gapScale).excitedFinrank i))))
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

/-- Enter the canonical strict-coefficient transfer theorem after generating
that strictness from exact plaquette profiles. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapExactPlaquetteTransferOrbitContractionData.toStrictTransferData
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapExactPlaquetteTransferOrbitContractionData
        W) :
    FiniteWilsonOSAutomaticExactGapCanonicalDobrushinStrictTransferOrbitContractionData
      W :=
  { Observable := D.Observable
    strictData := D.profileData.strictFamilyData
    gapScale := D.gapScale
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

/-- Exact finite plaquette-profile strictness generates the finite-scale
transfer-orbit connected-correlation estimate. -/
theorem finite_wilson_exact_gap_bound_of_exact_plaquette_profile
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapExactPlaquetteTransferOrbitContractionData
        W)
    (n : ℕ) (O : D.Observable) (r : ℕ) :
    ‖(W.system (D.scale n)).gibbsConnectedCorrelation
        (D.leftObservable n O) (D.rightObservable n O r)‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_bound_of_canonical_dobrushin_strictness
    D.toStrictTransferData n O r

/-- Under the explicit correlation representation and pointwise convergence
assumptions, exact plaquette-profile strictness at every finite scale yields the
continuum exact-gap connected-correlation decay estimate. -/
theorem finite_wilson_exact_gap_exact_plaquette_continuum_bound
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D :
      FiniteWilsonOSAutomaticExactGapExactPlaquetteTransferOrbitContractionData
        W)
    (O : D.Observable) (r : ℕ) :
    ‖D.continuumConnectedCorrelation O r‖ ≤
      D.decayAmplitude O * exactGapClusterContractionRatio ^ r :=
  finite_wilson_exact_gap_canonical_dobrushin_strict_continuum_bound
    D.toStrictTransferData O r

end

end MathlibAnalytic
end MGAP4D
