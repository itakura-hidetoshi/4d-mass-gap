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

/-- Boundary slot one is the opposite-side canonical plaquette for the second
axis of the ordered coordinate plane. -/
theorem periodicHypercubic_boundary_one_incident_exists
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    ∃ transverse : PeriodicHypercubicOtherAxis
        (periodicHypercubicPhysicalBoundaryEdge n p 1).2,
      periodicHypercubicIncidentPlaquette n
          (periodicHypercubicPhysicalBoundaryEdge n p 1)
          transverse true = p := by
  rcases p with ⟨x, ⟨⟨mu, nu⟩, hlt⟩⟩
  have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
  refine ⟨⟨mu, ne_of_lt hlt⟩, ?_⟩
  simp [periodicHypercubicPhysicalBoundaryEdge,
    periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hnot]

/-- Boundary slot two is the opposite-side canonical plaquette for the first
axis of the ordered coordinate plane. -/
theorem periodicHypercubic_boundary_two_incident_exists
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    ∃ transverse : PeriodicHypercubicOtherAxis
        (periodicHypercubicPhysicalBoundaryEdge n p 2).2,
      periodicHypercubicIncidentPlaquette n
          (periodicHypercubicPhysicalBoundaryEdge n p 2)
          transverse true = p := by
  rcases p with ⟨x, ⟨⟨mu, nu⟩, hlt⟩⟩
  refine ⟨⟨nu, ne_of_gt hlt⟩, ?_⟩
  simp [periodicHypercubicPhysicalBoundaryEdge,
    periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hlt]

/-- Boundary slot three is the based-side canonical plaquette for the second
axis of the ordered coordinate plane. -/
theorem periodicHypercubic_boundary_three_incident_exists
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    ∃ transverse : PeriodicHypercubicOtherAxis
        (periodicHypercubicPhysicalBoundaryEdge n p 3).2,
      periodicHypercubicIncidentPlaquette n
          (periodicHypercubicPhysicalBoundaryEdge n p 3)
          transverse false = p := by
  rcases p with ⟨x, ⟨⟨mu, nu⟩, hlt⟩⟩
  have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
  refine ⟨⟨mu, ne_of_lt hlt⟩, ?_⟩
  simp [periodicHypercubicPhysicalBoundaryEdge,
    periodicHypercubicIncidentPlaquette,
    periodicHypercubicAxisPairOfNe, hnot]

/-- Every touching plaquette lies in the canonical six-element candidate
family.  The proof is the exhaustive four-slot boundary classification. -/
theorem periodicHypercubicPlaquette_mem_incidentPlaquettes_of_touches
    (n : ℕ) [NeZero n]
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n)
    (hTouches : periodicHypercubicPlaquetteTouchesEdge n p e) :
    p ∈ periodicHypercubicIncidentPlaquettes n e := by
  rcases hTouches with ⟨k, hk⟩
  fin_cases k
  · rw [← hk]
    rcases periodicHypercubic_boundary_zero_incident_exists n p with
      ⟨transverse, hclassification⟩
    rw [← hclassification]
    exact periodicHypercubicIncidentPlaquette_mem n _ transverse false
  · rw [← hk]
    rcases periodicHypercubic_boundary_one_incident_exists n p with
      ⟨transverse, hclassification⟩
    rw [← hclassification]
    exact periodicHypercubicIncidentPlaquette_mem n _ transverse true
  · rw [← hk]
    rcases periodicHypercubic_boundary_two_incident_exists n p with
      ⟨transverse, hclassification⟩
    rw [← hclassification]
    exact periodicHypercubicIncidentPlaquette_mem n _ transverse true
  · rw [← hk]
    rcases periodicHypercubic_boundary_three_incident_exists n p with
      ⟨transverse, hclassification⟩
    rw [← hclassification]
    exact periodicHypercubicIncidentPlaquette_mem n _ transverse false

/-- Exact classification of all plaquettes touching a physical link. -/
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

/-- In four dimensions, at most six plaquettes touch one physical link,
uniformly in the periodic volume. -/
theorem periodicHypercubicTouchingPlaquettes_card_le_six
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicTouchingPlaquettes n e).card ≤ 6 := by
  rw [periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes]
  exact periodicHypercubicIncidentPlaquettes_card_le_six n e

end

end MathlibAnalytic
end MGAP4D
