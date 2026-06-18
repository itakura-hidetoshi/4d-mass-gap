import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The physical link underlying one signed boundary incidence. -/
def periodicHypercubicPhysicalBoundaryEdge
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) (k : Fin 4) :
    PeriodicHypercubicEdge n :=
  (periodicHypercubicBoundaryStep n p k).edge

/-- A coordinate plaquette touches a physical link when one of its four signed
boundary incidences uses that link. -/
def periodicHypercubicPlaquetteTouchesEdge
    (n : ℕ) (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) : Prop :=
  ∃ k : Fin 4, periodicHypercubicPhysicalBoundaryEdge n p k = e

/-- Every member produced by the canonical transverse-axis/two-side
parametrization actually touches the original physical link. -/
theorem periodicHypercubicIncidentPlaquette_touches
    (n : ℕ) (e : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis e.2) (otherSide : Bool) :
    periodicHypercubicPlaquetteTouchesEdge n
      (periodicHypercubicIncidentPlaquette n e nu otherSide) e := by
  rcases e with ⟨x, mu⟩
  rcases nu with ⟨nu, hne⟩
  by_cases hlt : mu < nu
  · cases otherSide
    · refine ⟨0, ?_⟩
      change
        (x, (periodicHypercubicAxisPairOfNe mu nu hne).1.1) = (x, mu)
      simp [periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨2, ?_⟩
      change
        (periodicHypercubicShift n (periodicHypercubicUnshift n x nu)
            (periodicHypercubicAxisPairOfNe mu nu hne).1.2,
          (periodicHypercubicAxisPairOfNe mu nu hne).1.1) =
        (x, mu)
      simp [periodicHypercubicAxisPairOfNe, hlt]
  · cases otherSide
    · refine ⟨3, ?_⟩
      change
        (x, (periodicHypercubicAxisPairOfNe mu nu hne).1.2) = (x, mu)
      simp [periodicHypercubicAxisPairOfNe, hlt]
    · refine ⟨1, ?_⟩
      change
        (periodicHypercubicShift n (periodicHypercubicUnshift n x nu)
            (periodicHypercubicAxisPairOfNe mu nu hne).1.1,
          (periodicHypercubicAxisPairOfNe mu nu hne).1.2) =
        (x, mu)
      simp [periodicHypercubicAxisPairOfNe, hlt]

/-- Every plaquette in the finite canonical incidence family has genuine
physical-link support. -/
theorem periodicHypercubicIncidentPlaquettes_mem_touches
    (n : ℕ) [NeZero n] (e : PeriodicHypercubicEdge n)
    (p : PeriodicHypercubicPlaquette n)
    (hp : p ∈ periodicHypercubicIncidentPlaquettes n e) :
    periodicHypercubicPlaquetteTouchesEdge n p e := by
  classical
  unfold periodicHypercubicIncidentPlaquettes at hp
  rcases Finset.mem_image.mp hp with ⟨data, _hdata, rfl⟩
  exact periodicHypercubicIncidentPlaquette_touches n e data.1 data.2

end

end MathlibAnalytic
end MGAP4D
