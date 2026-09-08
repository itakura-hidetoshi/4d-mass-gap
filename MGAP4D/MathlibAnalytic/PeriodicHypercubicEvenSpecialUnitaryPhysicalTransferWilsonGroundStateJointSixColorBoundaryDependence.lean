import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointLeftRetainedSigmaCoordinateBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointRightRetainedSigmaCoordinateBridge
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If a function on a dependent product depends only on `s` and only on `t`,
then it depends only on their intersection.  The proof splices two inputs along
`s`; agreement on `s ∩ t` makes the splice invisible to both hypotheses. -/
theorem functionDependsOn_inter
    {ι : Type*}
    {α : ι → Type*}
    {β : Type*}
    {f : (∀ i, α i) → β}
    {s t : Set ι}
    (hs : Function.DependsOn f s)
    (ht : Function.DependsOn f t) :
    Function.DependsOn f (s ∩ t) := by
  intro x y hxy
  classical
  let z : ∀ i, α i := fun i => if hi : i ∈ s then x i else y i
  calc
    f x = f z := hs (by
      intro i hi
      simp [z, hi])
    _ = f y := ht (by
      intro i hi
      by_cases his : i ∈ s
      · simp [z, his, hxy i ⟨his, hi⟩]
      · simp [z, his])

/-- For a six-indexed family of coordinate supports, dependence on every
support implies dependence on their total intersection. -/
theorem functionDependsOn_iInter_finSix
    {ι : Type*}
    {α : ι → Type*}
    {β : Type*}
    {f : (∀ i, α i) → β}
    (s : Fin 6 → Set ι)
    (h : ∀ c : Fin 6, Function.DependsOn f (s c)) :
    Function.DependsOn f (⋂ c : Fin 6, s c) := by
  have h01 := functionDependsOn_inter (h (0 : Fin 6)) (h (1 : Fin 6))
  have h012 := functionDependsOn_inter h01 (h (2 : Fin 6))
  have h0123 := functionDependsOn_inter h012 (h (3 : Fin 6))
  have h01234 := functionDependsOn_inter h0123 (h (4 : Fin 6))
  have h012345 := functionDependsOn_inter h01234 (h (5 : Fin 6))
  have hsets :
      (((((s (0 : Fin 6) ∩ s (1 : Fin 6)) ∩ s (2 : Fin 6)) ∩ s (3 : Fin 6)) ∩
        s (4 : Fin 6)) ∩ s (5 : Fin 6)) = ⋂ c : Fin 6, s c := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ c
      fin_cases c <;> assumption
    · intro hall
      exact ⟨⟨⟨⟨⟨hall 0, hall 1⟩, hall 2⟩, hall 3⟩, hall 4⟩, hall 5⟩
  rw [← hsets]
  exact h012345

/-- Dependence on every right-update retained coordinate support collapses
exactly to dependence on the left-boundary coordinates. -/
theorem periodicHypercubicEvenGroundStateJoint_dependsOn_leftBoundary_of_rightSix
    (H : ℕ)
    {Gauge β : Type*}
    (f :
      (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H → Gauge) → β)
    (h : ∀ c : Fin 6,
      Function.DependsOn f
        (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)) :
    Function.DependsOn f
      (periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H) := by
  have hInter := functionDependsOn_iInter_finSix
    (f := f)
    (fun c => periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)
    h
  rw [periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet_iInter_eq_leftBoundary H]
    at hInter
  exact hInter

/-- Symmetrically, dependence on every left-update retained coordinate support
collapses exactly to dependence on the right-boundary coordinates. -/
theorem periodicHypercubicEvenGroundStateJoint_dependsOn_rightBoundary_of_leftSix
    (H : ℕ)
    {Gauge β : Type*}
    (f :
      (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H → Gauge) → β)
    (h : ∀ c : Fin 6,
      Function.DependsOn f
        (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)) :
    Function.DependsOn f
      (periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H) := by
  have hInter := functionDependsOn_iInter_finSix
    (f := f)
    (fun c => periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)
    h
  rw [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet_iInter_eq_rightBoundary H]
    at hInter
  exact hInter

end

end MathlibAnalytic
end MGAP4D
