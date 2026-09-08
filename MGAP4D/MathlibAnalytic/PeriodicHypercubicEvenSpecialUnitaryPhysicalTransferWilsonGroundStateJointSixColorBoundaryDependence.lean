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
    (hs : DependsOn f s)
    (ht : DependsOn f t) :
    DependsOn f (s ∩ t) := by
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
    (h : ∀ c : Fin 6, DependsOn f (s c)) :
    DependsOn f (⋂ c : Fin 6, s c) := by
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
      DependsOn f
        (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c)) :
    DependsOn f
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
      DependsOn f
        (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)) :
    DependsOn f
      (periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H) := by
  have hInter := functionDependsOn_iInter_finSix
    (f := f)
    (fun c => periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c)
    h
  rw [periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet_iInter_eq_rightBoundary H]
    at hInter
  exact hInter

local instance groundStateSixColorBoundaryDependenceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- On the actual two-boundary pair presentation, if a function factors
through every right-color retained-coordinate restriction, then it factors
through the complete left boundary alone. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_factorsThrough_fst_of_rightSix
    (H N : ℕ)
    {β : Type*}
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → β)
    (h : ∀ c : Fin 6,
      Function.FactorsThrough f
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction
          H N c)) :
    Function.FactorsThrough f Prod.fst := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  let g :
      (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → β :=
    fun x => f (E.symm x)
  have hg : ∀ c : Fin 6,
      DependsOn g
        (periodicHypercubicEvenGroundStateJointRightRetainedCoordinateSet H c) := by
    intro c x y hxy
    apply h c
    funext i
    simpa [periodicHypercubicEvenSpecialUnitaryGroundStateJointRightRetainedCoordinateRestriction,
      E] using hxy i.1 i.2
  have hgLeft :=
    periodicHypercubicEvenGroundStateJoint_dependsOn_leftBoundary_of_rightSix H g hg
  intro z₁ z₂ hz
  have hcoord :
      ∀ i ∈ periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet H,
        E z₁ i = E z₂ i := by
    intro i hi
    cases i with
    | inl e =>
        simpa [E] using congrFun hz e
    | inr e =>
        simp [periodicHypercubicEvenGroundStateJointLeftBoundaryCoordinateSet] at hi
  have heq : g (E z₁) = g (E z₂) := hgLeft hcoord
  simpa [g, E] using heq

/-- Symmetrically, factoring through every left-color retained-coordinate
restriction forces factorization through the complete right boundary alone. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJoint_factorsThrough_snd_of_leftSix
    (H N : ℕ)
    {β : Type*}
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → β)
    (h : ∀ c : Fin 6,
      Function.FactorsThrough f
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction
          H N c)) :
    Function.FactorsThrough f Prod.snd := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv H N
  let g :
      (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → β :=
    fun x => f (E.symm x)
  have hg : ∀ c : Fin 6,
      DependsOn g
        (periodicHypercubicEvenGroundStateJointLeftRetainedCoordinateSet H c) := by
    intro c x y hxy
    apply h c
    funext i
    simpa [periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftRetainedCoordinateRestriction,
      E] using hxy i.1 i.2
  have hgRight :=
    periodicHypercubicEvenGroundStateJoint_dependsOn_rightBoundary_of_leftSix H g hg
  intro z₁ z₂ hz
  have hcoord :
      ∀ i ∈ periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet H,
        E z₁ i = E z₂ i := by
    intro i hi
    cases i with
    | inl e =>
        simp [periodicHypercubicEvenGroundStateJointRightBoundaryCoordinateSet] at hi
    | inr e =>
        simpa [E] using congrFun hz e
  have heq : g (E z₁) = g (E z₂) := hgRight hcoord
  simpa [g, E] using heq

end

end MathlibAnalytic
end MGAP4D
