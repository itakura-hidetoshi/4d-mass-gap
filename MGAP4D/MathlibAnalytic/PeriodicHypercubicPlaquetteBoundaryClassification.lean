import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceExact

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The based plaquette in an ordered `mu`-`nu` plane is recovered from its
slot-zero physical link and transverse direction `nu`. -/
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

/-- Slot one traverses the second-axis link on the opposite side of the
plaquette. -/
theorem periodicHypercubic_boundary_one_incident_eq
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis)
    (hlt : mu < nu) :
    periodicHypercubicIncidentPlaquette n
        (periodicHypercubicShift n x mu, nu)
        ⟨mu, ne_of_lt hlt⟩ true =
      (x, ⟨(mu, nu), hlt⟩) := by
  have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
  simp [periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hnot]

/-- Slot two traverses the first-axis link backwards on the opposite side. -/
theorem periodicHypercubic_boundary_two_incident_eq
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis)
    (hlt : mu < nu) :
    periodicHypercubicIncidentPlaquette n
        (periodicHypercubicShift n x nu, mu)
        ⟨nu, ne_of_gt hlt⟩ true =
      (x, ⟨(mu, nu), hlt⟩) := by
  simp [periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hlt]

/-- Slot three traverses the based second-axis link backwards. -/
theorem periodicHypercubic_boundary_three_incident_eq
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis)
    (hlt : mu < nu) :
    periodicHypercubicIncidentPlaquette n (x, nu)
        ⟨mu, ne_of_lt hlt⟩ false =
      (x, ⟨(mu, nu), hlt⟩) := by
  have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
  simp [periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hnot]

end

end MathlibAnalytic
end MGAP4D
