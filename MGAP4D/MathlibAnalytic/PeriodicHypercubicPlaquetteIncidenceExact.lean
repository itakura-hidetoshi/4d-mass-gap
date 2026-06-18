import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every canonical incident plaquette belongs to the finite incidence family. -/
theorem periodicHypercubicIncidentPlaquette_mem
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis e.2)
    (otherSide : Bool) :
    periodicHypercubicIncidentPlaquette n e nu otherSide ∈
      periodicHypercubicIncidentPlaquettes n e := by
  classical
  unfold periodicHypercubicIncidentPlaquettes
  apply Finset.mem_image.mpr
  exact ⟨(nu, otherSide), Finset.mem_univ _, rfl⟩

/-- Conversely, every coordinate plaquette touching a physical link is one of
its three-transverse-directions times two-sides canonical plaquettes. -/
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
    subst e
    unfold periodicHypercubicIncidentPlaquettes
    apply Finset.mem_image.mpr
    refine ⟨(⟨nu, ne_of_gt hlt⟩, false), Finset.mem_univ _, ?_⟩
    simp [periodicHypercubicIncidentPlaquette,
      periodicHypercubicAxisPairOfNe, hlt]
  · have he : (periodicHypercubicShift n x mu, nu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    subst e
    have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
    unfold periodicHypercubicIncidentPlaquettes
    apply Finset.mem_image.mpr
    refine ⟨(⟨mu, ne_of_lt hlt⟩, true), Finset.mem_univ _, ?_⟩
    simp [periodicHypercubicIncidentPlaquette,
      periodicHypercubicAxisPairOfNe, hnot]
  · have he : (periodicHypercubicShift n x nu, mu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    subst e
    unfold periodicHypercubicIncidentPlaquettes
    apply Finset.mem_image.mpr
    refine ⟨(⟨nu, ne_of_gt hlt⟩, true), Finset.mem_univ _, ?_⟩
    simp [periodicHypercubicIncidentPlaquette,
      periodicHypercubicAxisPairOfNe, hlt]
  · have he : (x, nu) = e := by
      simpa [periodicHypercubicPhysicalBoundaryEdge] using hk
    subst e
    have hnot : ¬ nu < mu := not_lt_of_ge (le_of_lt hlt)
    unfold periodicHypercubicIncidentPlaquettes
    apply Finset.mem_image.mpr
    refine ⟨(⟨mu, ne_of_lt hlt⟩, false), Finset.mem_univ _, ?_⟩
    simp [periodicHypercubicIncidentPlaquette,
      periodicHypercubicAxisPairOfNe, hnot]

/-- The actual finite set of coordinate plaquettes touching a physical link. -/
noncomputable def periodicHypercubicTouchingPlaquettes
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n) :
    Finset (PeriodicHypercubicPlaquette n) := by
  classical
  exact Finset.univ.filter fun p =>
    periodicHypercubicPlaquetteTouchesEdge n p e

@[simp]
theorem periodicHypercubic_mem_touchingPlaquettes_iff
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n)
    (p : PeriodicHypercubicPlaquette n) :
    p ∈ periodicHypercubicTouchingPlaquettes n e ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  classical
  simp [periodicHypercubicTouchingPlaquettes]

/-- Exact classification: the actual touching set equals the canonical
three-directions times two-sides family. -/
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

/-- In four dimensions, at most six coordinate plaquettes touch any physical
link, independently of the periodic volume. -/
theorem periodicHypercubicTouchingPlaquettes_card_le_six
    (n : ℕ) [NeZero n]
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicTouchingPlaquettes n e).card ≤ 6 := by
  rw [periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes]
  exact periodicHypercubicIncidentPlaquettes_card_le_six n e

end

end MathlibAnalytic
end MGAP4D
