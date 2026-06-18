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

end

end MathlibAnalytic
end MGAP4D
