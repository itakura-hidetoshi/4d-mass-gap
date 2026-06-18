import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The three non-target physical links in the canonical plaquette determined
by a target link, one transverse axis, and one of the two sides.  The
enumeration is independent of the ordering used for the coordinate-plane
label. -/
def periodicHypercubicIncidentOtherEdge
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool)
    (slot : Fin 3) : PeriodicHypercubicEdge n :=
  if otherSide then
    match slot.1 with
    | 0 => (periodicHypercubicUnshift n target.1 nu.1, nu.1)
    | 1 =>
        (periodicHypercubicShift n
            (periodicHypercubicUnshift n target.1 nu.1) target.2,
          nu.1)
    | _ => (periodicHypercubicUnshift n target.1 nu.1, target.2)
  else
    match slot.1 with
    | 0 => (target.1, nu.1)
    | 1 => (periodicHypercubicShift n target.1 target.2, nu.1)
    | _ => (periodicHypercubicShift n target.1 nu.1, target.2)

@[simp] theorem periodicHypercubicIncidentOtherEdge_false_zero
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu false 0 =
      (target.1, nu.1) :=
  rfl

@[simp] theorem periodicHypercubicIncidentOtherEdge_false_one
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu false 1 =
      (periodicHypercubicShift n target.1 target.2, nu.1) :=
  rfl

@[simp] theorem periodicHypercubicIncidentOtherEdge_false_two
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu false 2 =
      (periodicHypercubicShift n target.1 nu.1, target.2) :=
  rfl

@[simp] theorem periodicHypercubicIncidentOtherEdge_true_zero
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu true 0 =
      (periodicHypercubicUnshift n target.1 nu.1, nu.1) :=
  rfl

@[simp] theorem periodicHypercubicIncidentOtherEdge_true_one
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu true 1 =
      (periodicHypercubicShift n
          (periodicHypercubicUnshift n target.1 nu.1) target.2,
        nu.1) :=
  rfl

@[simp] theorem periodicHypercubicIncidentOtherEdge_true_two
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentOtherEdge n target nu true 2 =
      (periodicHypercubicUnshift n target.1 nu.1, target.2) :=
  rfl

/-- Every physical link other than the target that lies on a canonical
incident plaquette is one of its three explicitly enumerated other links. -/
theorem periodicHypercubicIncidentPlaquette_other_edge_classification
    (n : ℕ)
    (target source : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool)
    (hTouches :
      periodicHypercubicPlaquetteTouchesEdge n
        (periodicHypercubicIncidentPlaquette n target nu otherSide) source)
    (hNe : source ≠ target) :
    ∃ slot : Fin 3,
      periodicHypercubicIncidentOtherEdge n target nu otherSide slot = source := by
  rcases target with ⟨x, mu⟩
  rcases nu with ⟨nu, hnu⟩
  rcases hTouches with ⟨k, hk⟩
  by_cases hlt : mu < nu
  · cases otherSide
    · fin_cases k
      · exfalso
        apply hNe
        simpa [periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk.symm
      · refine ⟨1, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨2, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨0, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
    · fin_cases k
      · refine ⟨2, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨1, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · exfalso
        apply hNe
        simpa [periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk.symm
      · refine ⟨0, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
  · cases otherSide
    · fin_cases k
      · refine ⟨0, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨2, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨1, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · exfalso
        apply hNe
        simpa [periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk.symm
    · fin_cases k
      · refine ⟨0, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · exfalso
        apply hNe
        simpa [periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk.symm
      · refine ⟨1, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk
      · refine ⟨2, ?_⟩
        simpa [periodicHypercubicIncidentOtherEdge,
          periodicHypercubicPhysicalBoundaryEdge,
          periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt] using hk

end

end MathlibAnalytic
end MGAP4D
