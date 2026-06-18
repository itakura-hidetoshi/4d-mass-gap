import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteBoundaryClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every coordinate plaquette touching a physical link belongs to its
canonical three-transverse-directions times two-sides family. -/
theorem periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n)
    (hTouches : periodicHypercubicPlaquetteTouchesEdge n p e) :
    p ∈ periodicHypercubicIncidentPlaquettes n e := by
  classical
  rcases p with ⟨x, ⟨⟨mu, nu⟩, hlt⟩⟩
  rcases hTouches with ⟨k, hk⟩
  fin_cases k
  · have he : (x, mu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    rw [← he]
    have hmem := periodicHypercubicIncidentPlaquette_mem n
      (x, mu) ⟨nu, ne_of_gt hlt⟩ false
    rw [periodicHypercubic_boundary_zero_incident_eq n x mu nu hlt] at hmem
    exact hmem
  · have he : (periodicHypercubicShift n x mu, nu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    rw [← he]
    have hmem := periodicHypercubicIncidentPlaquette_mem n
      (periodicHypercubicShift n x mu, nu)
      ⟨mu, ne_of_lt hlt⟩ true
    rw [periodicHypercubic_boundary_one_incident_eq n x mu nu hlt] at hmem
    exact hmem
  · have he : (periodicHypercubicShift n x nu, mu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    rw [← he]
    have hmem := periodicHypercubicIncidentPlaquette_mem n
      (periodicHypercubicShift n x nu, mu)
      ⟨nu, ne_of_gt hlt⟩ true
    rw [periodicHypercubic_boundary_two_incident_eq n x mu nu hlt] at hmem
    exact hmem
  · have he : (x, nu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    rw [← he]
    have hmem := periodicHypercubicIncidentPlaquette_mem n
      (x, nu) ⟨mu, ne_of_lt hlt⟩ false
    rw [periodicHypercubic_boundary_three_incident_eq n x mu nu hlt] at hmem
    exact hmem

/-- Exact classification of the actual touching set. -/
theorem periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n) :
    periodicHypercubicTouchingPlaquettes n e =
      periodicHypercubicIncidentPlaquettes n e := by
  classical
  apply Finset.ext
  intro p
  rw [periodicHypercubic_mem_touchingPlaquettes_iff]
  constructor
  · exact periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches n p e
  · intro hp
    exact periodicHypercubicIncidentPlaquettes_mem_touches n e p hp

/-- In four dimensions, at most six coordinate plaquettes touch one physical
link, uniformly in the periodic volume. -/
theorem periodicHypercubicTouchingPlaquettes_card_le_six
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicTouchingPlaquettes n e).card ≤ 6 := by
  rw [periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes]
  exact periodicHypercubicIncidentPlaquettes_card_le_six n e

end

end MathlibAnalytic
end MGAP4D
