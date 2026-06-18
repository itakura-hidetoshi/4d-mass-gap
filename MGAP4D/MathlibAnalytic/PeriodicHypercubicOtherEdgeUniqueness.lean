import MGAP4D.MathlibAnalytic.PeriodicHypercubicIncidentOtherEdgeClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Translation by one fixed positive coordinate unit is injective on periodic
vertices. -/
theorem periodicHypercubicShift_vertex_injective
    (n : ℕ) (mu : PeriodicHypercubicAxis) :
    Function.Injective
      (fun x : PeriodicHypercubicVertex n =>
        periodicHypercubicShift n x mu) := by
  intro x y h
  unfold periodicHypercubicShift at h
  exact add_right_cancel h

/-- Translation by one fixed negative coordinate unit is injective on periodic
vertices. -/
theorem periodicHypercubicUnshift_vertex_injective
    (n : ℕ) (mu : PeriodicHypercubicAxis) :
    Function.Injective
      (fun x : PeriodicHypercubicVertex n =>
        periodicHypercubicUnshift n x mu) := by
  intro x y h
  have hAdd :
      x + (-periodicHypercubicUnit n mu) =
        y + (-periodicHypercubicUnit n mu) := by
    simpa [periodicHypercubicUnshift, sub_eq_add_neg] using h
  exact add_right_cancel hAdd

@[simp] theorem periodicHypercubicShift_eq_shift_iff
    (n : ℕ)
    (mu : PeriodicHypercubicAxis)
    (x y : PeriodicHypercubicVertex n) :
    periodicHypercubicShift n x mu =
        periodicHypercubicShift n y mu ↔
      x = y := by
  constructor
  · exact periodicHypercubicShift_vertex_injective n mu
  · intro h
    rw [h]

@[simp] theorem periodicHypercubicUnshift_eq_unshift_iff
    (n : ℕ)
    (mu : PeriodicHypercubicAxis)
    (x y : PeriodicHypercubicVertex n) :
    periodicHypercubicUnshift n x mu =
        periodicHypercubicUnshift n y mu ↔
      x = y := by
  constructor
  · exact periodicHypercubicUnshift_vertex_injective n mu
  · intro h
    rw [h]

/-- Moving negatively in one direction and then positively in another cannot
return to the starting vertex when the two directions differ and the periodic
side length is nondegenerate. -/
theorem periodicHypercubicShift_unshift_other_ne_self
    (n : ℕ) (hn : 2 ≤ n)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis)
    (hne : mu ≠ nu) :
    periodicHypercubicShift n
        (periodicHypercubicUnshift n x nu) mu ≠ x := by
  intro h
  have hShifted := congrArg
    (fun y : PeriodicHypercubicVertex n =>
      periodicHypercubicShift n y nu) h
  have hAxes :
      periodicHypercubicShift n x mu =
        periodicHypercubicShift n x nu := by
    calc
      periodicHypercubicShift n x mu =
          periodicHypercubicShift n
            (periodicHypercubicShift n
              (periodicHypercubicUnshift n x nu) nu) mu := by
            rw [periodicHypercubicShift_unshift]
      _ = periodicHypercubicShift n
            (periodicHypercubicShift n
              (periodicHypercubicUnshift n x nu) mu) nu := by
            exact (periodicHypercubicShift_comm n
              (periodicHypercubicUnshift n x nu) nu mu)
      _ = periodicHypercubicShift n x nu := hShifted
  exact hne (periodicHypercubicShift_axis_injective n hn x hAxes)

/-- The vertex component of the four transverse non-target links for one fixed
transverse axis. -/
def periodicHypercubicIncidentTransverseVertex
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2)
    (otherSide : Bool)
    (slot : Fin 2) : PeriodicHypercubicVertex n :=
  if otherSide then
    match slot.1 with
    | 0 => periodicHypercubicUnshift n target.1 nu.1
    | _ => periodicHypercubicShift n
        (periodicHypercubicUnshift n target.1 nu.1) target.2
  else
    match slot.1 with
    | 0 => target.1
    | _ => periodicHypercubicShift n target.1 target.2

@[simp] theorem periodicHypercubicIncidentTransverseVertex_false_zero
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentTransverseVertex n target nu false 0 =
      target.1 :=
  rfl

@[simp] theorem periodicHypercubicIncidentTransverseVertex_false_one
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentTransverseVertex n target nu false 1 =
      periodicHypercubicShift n target.1 target.2 :=
  rfl

@[simp] theorem periodicHypercubicIncidentTransverseVertex_true_zero
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentTransverseVertex n target nu true 0 =
      periodicHypercubicUnshift n target.1 nu.1 :=
  rfl

@[simp] theorem periodicHypercubicIncidentTransverseVertex_true_one
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    periodicHypercubicIncidentTransverseVertex n target nu true 1 =
      periodicHypercubicShift n
        (periodicHypercubicUnshift n target.1 nu.1) target.2 :=
  rfl

/-- For a fixed transverse axis, the two sides and the two transverse boundary
positions give four distinct vertices when `3 ≤ n`. -/
theorem periodicHypercubicIncidentTransverseVertex_injective
    (n : ℕ) (hn : 3 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (nu : PeriodicHypercubicOtherAxis target.2) :
    Function.Injective
      (fun data : Bool × Fin 2 =>
        periodicHypercubicIncidentTransverseVertex n target nu
          data.1 data.2) := by
  rcases target with ⟨x, mu⟩
  rcases nu with ⟨nu, hnu⟩
  intro a b h
  rcases a with ⟨sideA, slotA⟩
  rcases b with ⟨sideB, slotB⟩
  cases sideA <;> cases sideB <;>
    fin_cases slotA <;> fin_cases slotB <;>
    simp_all [periodicHypercubicIncidentTransverseVertex,
      periodicHypercubicShift_ne_self,
      periodicHypercubicUnshift_ne_self,
      periodicHypercubicShift_ne_unshift,
      periodicHypercubicShift_unshift_other_ne_self]

end

end MathlibAnalytic
end MGAP4D
