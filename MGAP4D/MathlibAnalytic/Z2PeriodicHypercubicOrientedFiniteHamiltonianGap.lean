import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedExplicitDobrushin
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every element of the actual multiplicative `Z₂` gauge group is self-inverse. -/
@[simp] theorem z2Gauge_inv_eq_self
    (g : Z2Gauge) :
    g⁻¹ = g := by
  fin_cases g <;> native_decide

/-- Finite proxy carrying the exact physical-link oriented `Z₂` Wilson action. -/
def z2PeriodicHypercubicOrientedUnsignedProxy
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    FiniteLatticeWilsonSystem :=
  (z2PeriodicHypercubicOrientedWilsonSystem
    n beta hBeta).unsignedProxy

/-- The explicit small-coupling condition generates a proof-relevant
Dobrushin matrix on the action-equivalent finite proxy. -/
noncomputable def
    z2PeriodicHypercubicOrientedCanonicalDobrushinMatrixData
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2) :
    FiniteLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta) :=
  finiteOrientedLatticeWilsonCanonicalDobrushinMatrixDataOnUnsignedProxy
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
    z2Gauge_inv_eq_self
    (z2PeriodicHypercubicOrientedIncidenceCertificate
      n hn beta hBeta).edgeCard_pos
    (z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one_of_beta_lt
      n hn beta hBeta hBetaLt)

/-- The centered random-scan Rayleigh certificate is generated without an
additional spectral assumption. -/
noncomputable def
    z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2) :
    FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      (z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta) :=
  finiteLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
    (z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta)
    (z2PeriodicHypercubicOrientedCanonicalDobrushinMatrixData
      n hn beta hBeta hBetaLt)
    (z2PeriodicHypercubicOrientedIncidenceCertificate
      n hn beta hBeta).edgeCard_pos

/-- The explicit periodic oriented `Z₂` condition gives the unscaled finite
heat-bath Poincare inequality. -/
theorem z2PeriodicHypercubicOriented_heatBath_poincare
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2)
    (f :
      (z2PeriodicHypercubicOrientedUnsignedProxy
        n beta hBeta).Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap
        (z2PeriodicHypercubicOrientedCanonicalDobrushinMatrixData
          n hn beta hBeta hBetaLt) *
      (z2PeriodicHypercubicOrientedUnsignedProxy
        n beta hBeta).gibbsVarianceReal f ≤
      (z2PeriodicHypercubicOrientedUnsignedProxy
        n beta hBeta).singleLinkHeatBathDirichletForm f :=
  finite_lattice_dobrushinHeatBathGap_mul_variance_le_dirichlet
    (z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta)
    (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
      n hn beta hBeta hBetaLt)
    f

/-- The normalized finite heat-bath Hamiltonian has the repository's public
exact lower bound on the vacuum-orthogonal sector. -/
theorem z2PeriodicHypercubicOriented_finiteHamiltonian_gap
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2)
    (x :
      (z2PeriodicHypercubicOrientedUnsignedProxy
        n beta hBeta).GibbsHilbertSpace)
    (hx : x ∈
      finiteVacuumOrthogonal
        (z2PeriodicHypercubicOrientedUnsignedProxy
          n beta hBeta).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta).
          gibbsDobrushinScaledHeatBathHamiltonianLinearMap
            (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
              n hn beta hBeta hBetaLt)
          x)
        x :=
  finite_lattice_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    (z2PeriodicHypercubicOrientedUnsignedProxy n beta hBeta)
    (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
      n hn beta hBeta hBetaLt)
    x hx

end

end MathlibAnalytic
end MGAP4D
