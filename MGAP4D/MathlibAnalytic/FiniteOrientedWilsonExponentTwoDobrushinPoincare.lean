import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyDirichlet
import MGAP4D.MathlibAnalytic.FiniteWilsonDobrushinScaledHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A proxy Dobrushin Rayleigh certificate gives the same unnormalized
Poincare inequality for the native exponent-two oriented system. -/
theorem finite_oriented_dobrushinHeatBathGap_mul_variance_le_dirichlet
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy)
    (f : L.Configuration → ℝ) :
    finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f := by
  calc
    finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.gibbsVarianceReal f =
      finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
        L.unsignedProxy.gibbsVarianceReal f := by
          rw [finite_oriented_unsignedProxy_gibbsVarianceReal_eq
            L hInv f]
    _ ≤ L.unsignedProxy.singleLinkHeatBathDirichletForm f :=
      finite_lattice_dobrushinHeatBathGap_mul_variance_le_dirichlet
        L.unsignedProxy C f
    _ = L.singleLinkHeatBathDirichletForm f :=
      finite_oriented_unsignedProxy_singleLinkHeatBathDirichletForm_eq
        L hInv f

/-- After the explicit positive normalization, the native exponent-two
Dirichlet form carries the repository's public exact-gap coefficient. -/
theorem finite_oriented_exactGap_mul_variance_le_dobrushinScale_mul_dirichlet
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (C : FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy)
    (f : L.Configuration → ℝ) :
    exactGapValueReal * L.gibbsVarianceReal f ≤
      finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm f := by
  have hScaleNonneg :
      0 ≤ finiteLatticeWilsonDobrushinNormalizedScale C.matrixData :=
    le_of_lt (finite_lattice_dobrushinNormalizedScale_pos C.matrixData)
  calc
    exactGapValueReal * L.gibbsVarianceReal f =
        (finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
          finiteLatticeWilsonDobrushinHeatBathGap C.matrixData) *
            L.gibbsVarianceReal f := by
      rw [finite_lattice_dobrushinNormalizedScale_mul_heatBathGap]
    _ = finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        (finiteLatticeWilsonDobrushinHeatBathGap C.matrixData *
          L.gibbsVarianceReal f) := by
      ring
    _ ≤ finiteLatticeWilsonDobrushinNormalizedScale C.matrixData *
        L.singleLinkHeatBathDirichletForm f :=
      mul_le_mul_of_nonneg_left
        (finite_oriented_dobrushinHeatBathGap_mul_variance_le_dirichlet
          L hInv C f)
        hScaleNonneg

end

end MathlibAnalytic
end MGAP4D
