import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonRandomScanRayleighSpectralLift
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonDobrushinHamiltonianGap
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonFourDimensionalDobrushinMatrixCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every strict orientation-correct Dobrushin matrix yields the unnormalized
finite heat-bath Hamiltonian coercivity on centered observables. -/
theorem finite_oriented_canonical_dobrushinHeatBathGap_mul_self_le_hamiltonian
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ)
    (hCentered : L.gibbsExpectationReal f = 0) :
    finiteOrientedLatticeWilsonDobrushinHeatBathGap D *
        L.gibbsPairingReal f f ≤
      L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f := by
  exact finite_oriented_dobrushinHeatBathGap_mul_self_le_hamiltonian
    L
    (finiteOrientedLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
      L D hEdge)
    f hCentered

/-- A certified four-dimensional orientation-correct incidence geometry and a
strict likelihood-ratio threshold yield a concrete finite-volume Hamiltonian
coercivity estimate. -/
theorem
    FiniteOrientedWilsonFourDimensionalIncidenceCertificate.dobrushinHeatBathGap_mul_self_le_hamiltonian_of_expRatioBound
    {L : FiniteOrientedLatticeWilsonSystem}
    (I : FiniteOrientedWilsonFourDimensionalIncidenceCertificate L)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : L.ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹)
    (f : L.Configuration → ℝ)
    (hCentered : L.gibbsExpectationReal f = 0) :
    let D := I.canonicalDobrushinMatrixData_of_expRatioBound
      R hR hRatio hThreshold
    finiteOrientedLatticeWilsonDobrushinHeatBathGap D *
        L.gibbsPairingReal f f ≤
      L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f := by
  dsimp
  exact finite_oriented_canonical_dobrushinHeatBathGap_mul_self_le_hamiltonian
    L
    (I.canonicalDobrushinMatrixData_of_expRatioBound
      R hR hRatio hThreshold)
    I.edgeCard_pos f hCentered

/-- The periodic four-dimensional orientation-correct `Z₂` Wilson system has
a concrete finite-volume heat-bath coercivity estimate whenever its exact
conditional likelihood-ratio radius satisfies the certified threshold. -/
theorem z2PeriodicHypercubicOriented_dobrushinHeatBathGap_mul_self_le_hamiltonian
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).
        ActiveConditionalExpRatioBound R)
    (hThreshold :
      (Real.exp R - 1) / (Real.exp R + 1) < (18 : ℝ)⁻¹)
    (f : (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).
      Configuration)
    (hCentered :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).
        gibbsExpectationReal f = 0) :
    let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
    let D := z2PeriodicHypercubicOriented_canonicalDobrushinMatrixData
      n hn beta hBeta R hR hRatio hThreshold
    finiteOrientedLatticeWilsonDobrushinHeatBathGap D *
        L.gibbsPairingReal f f ≤
      L.gibbsPairingReal
        (L.singleLinkHeatBathHamiltonianObservable f) f := by
  dsimp
  exact
    (z2PeriodicHypercubicOrientedIncidenceCertificate n hn beta hBeta).
      dobrushinHeatBathGap_mul_self_le_hamiltonian_of_expRatioBound
        R hR hRatio hThreshold f hCentered

end
end MathlibAnalytic
end MGAP4D
