import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceExact

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The based plaquette in an ordered `mu`-`nu` plane is recovered from its
slot-zero physical link and the transverse direction `nu`. -/
theorem periodicHypercubic_boundary_zero_incident_eq
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis)
    (hlt : mu < nu) :
    periodicHypercubicIncidentPlaquette n (x, mu)
        ⟨nu, ne_of_gt hlt⟩ false =
      (x, ⟨(mu, nu), hlt⟩) := by
  simp [periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hlt]

end

end MathlibAnalytic
end MGAP4D
