import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceExact

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Boundary slot zero is the based-side canonical plaquette. -/
theorem periodicHypercubic_boundary_zero_incident_exists
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    ∃ transverse : PeriodicHypercubicOtherAxis
        (periodicHypercubicPhysicalBoundaryEdge n p 0).2,
      periodicHypercubicIncidentPlaquette n
          (periodicHypercubicPhysicalBoundaryEdge n p 0)
          transverse false = p := by
  rcases p with ⟨x, ⟨⟨mu, nu⟩, hlt⟩⟩
  refine ⟨⟨nu, ne_of_gt hlt⟩, ?_⟩
  simp [periodicHypercubicPhysicalBoundaryEdge,
    periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hlt]

end

end MathlibAnalytic
end MGAP4D
