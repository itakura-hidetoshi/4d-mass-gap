import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyConditional
import MGAP4D.MathlibAnalytic.FiniteWilsonDobrushinScaledHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Any proof-relevant oriented Dobrushin matrix transports to the unsigned
proxy when every gauge-group element is self-inverse. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.toUnsignedProxy
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g) :
    FiniteLatticeWilsonDobrushinMatrixData L.unsignedProxy :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    influence_diagonal_zero := D.influence_diagonal_zero
    conditionalTotalVariation_le := by
      intro target source A B hAgree
      rw [finite_oriented_unsignedProxy_singleLinkConditionalTotalVariation_eq
        L hInv A B target]
      exact D.conditionalTotalVariation_le target source A B
        ((finite_oriented_unsignedProxy_agreeOffLink_iff
          L A B source).mp hAgree)
    dobrushinCoefficient := D.dobrushinCoefficient
    dobrushinCoefficient_nonneg := D.dobrushinCoefficient_nonneg
    rowSum_le_coefficient := D.rowSum_le_coefficient
    dobrushinCoefficient_lt_one := D.dobrushinCoefficient_lt_one }

/-- A strict exact oriented canonical coefficient generates a legacy-compatible
matrix certificate on the action-equivalent proxy. -/
noncomputable def
    finiteOrientedLatticeWilsonCanonicalDobrushinMatrixDataOnUnsignedProxy
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteLatticeWilsonDobrushinMatrixData L.unsignedProxy :=
  (finiteOrientedLatticeWilsonCanonicalDobrushinMatrixData
    L hEdge hStrict).toUnsignedProxy hInv

/-- The exact oriented coefficient generates the existing spectral Rayleigh
certificate on the action-equivalent proxy. -/
noncomputable def
    finiteOrientedLatticeWilsonCanonicalRayleighCertificateOnUnsignedProxy
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1) :
    FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate
      L.unsignedProxy :=
  finiteLatticeWilsonCanonicalDobrushinRandomScanRayleighCertificate
    L.unsignedProxy
    (finiteOrientedLatticeWilsonCanonicalDobrushinMatrixDataOnUnsignedProxy
      L hInv hEdge hStrict)
    hEdge

/-- The normalized finite heat-bath Hamiltonian gap theorem applies to every
exponent-two oriented system with strict exact canonical coefficient. -/
theorem finite_oriented_unsignedProxy_dobrushinScaled_hamiltonian_gap
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (hEdge : 0 < Fintype.card L.Edge)
    (hStrict : L.canonicalDobrushinCoefficient hEdge < 1)
    (x : L.unsignedProxy.GibbsHilbertSpace)
    (hx : x ∈ finiteVacuumOrthogonal
      L.unsignedProxy.gibbsHilbertVacuum) :
    exactGapValueReal * ‖x‖ ^ 2 ≤
      inner ℝ
        (L.unsignedProxy.gibbsDobrushinScaledHeatBathHamiltonianLinearMap
          (finiteOrientedLatticeWilsonCanonicalRayleighCertificateOnUnsignedProxy
            L hInv hEdge hStrict)
          x)
        x :=
  finite_lattice_dobrushinScaled_hamiltonian_gap_on_vacuumOrthogonal
    L.unsignedProxy
    (finiteOrientedLatticeWilsonCanonicalRayleighCertificateOnUnsignedProxy
      L hInv hEdge hStrict)
    x hx

end

end MathlibAnalytic
end MGAP4D
