import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedFiniteHamiltonianGap
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonExponentTwoDobrushinScaledHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit periodic oriented `Z₂` condition gives the native unscaled
heat-bath Poincare inequality on physical positive links. -/
theorem z2PeriodicHypercubicOriented_native_heatBath_poincare
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2)
    (f :
      (z2PeriodicHypercubicOrientedWilsonSystem
        n beta hBeta).Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap
        (z2PeriodicHypercubicOrientedCanonicalDobrushinMatrixData
          n hn beta hBeta hBetaLt) *
      (z2PeriodicHypercubicOrientedWilsonSystem
        n beta hBeta).gibbsVarianceReal f ≤
      (z2PeriodicHypercubicOrientedWilsonSystem
        n beta hBeta).singleLinkHeatBathDirichletForm f :=
  finite_oriented_dobrushinHeatBathGap_mul_variance_le_dirichlet
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
    z2Gauge_inv_eq_self
    (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
      n hn beta hBeta hBetaLt)
    f

/-- The explicitly normalized native oriented `Z₂` heat-bath Hamiltonian has
the public exact lower bound on its vacuum-orthogonal sector. -/
theorem z2PeriodicHypercubicOriented_native_finiteHamiltonian_gap
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2)
    (x :
      (z2PeriodicHypercubicOrientedWilsonSystem
        n beta hBeta).GibbsHilbertSpace)
    (hx : x ∈
      finiteVacuumOrthogonal
        (z2PeriodicHypercubicOrientedWilsonSystem
          n beta hBeta).gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        ((z2PeriodicHypercubicOrientedWilsonSystem
          n beta hBeta).gibbsDobrushinScaledHeatBathHamiltonianLinearMap
            (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
              n hn beta hBeta hBetaLt)
          x)
        x :=
  finite_oriented_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
    z2Gauge_inv_eq_self
    (z2PeriodicHypercubicOrientedCanonicalRayleighCertificate
      n hn beta hBeta hBetaLt)
    x hx

end

end MathlibAnalytic
end MGAP4D
