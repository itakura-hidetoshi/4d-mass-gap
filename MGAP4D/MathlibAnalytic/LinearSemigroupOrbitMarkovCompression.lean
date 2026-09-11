import MGAP4D.MathlibAnalytic.LinearMarkovCompression
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Forward orbit paths for a real-linear semigroup. -/
abbrev LinearSemigroupOrbitSpace (E : Type*) := NNReal → E

/-- The canonical orbit path `s ↦ S_s x`. -/
def linearSemigroupOrbitLift
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (semigroup : NNReal → E →ₗ[ℝ] E) :
    E →ₗ[ℝ] LinearSemigroupOrbitSpace E where
  toFun := fun x s => semigroup s x
  map_add' := by
    intro x y
    ext s
    exact (semigroup s).map_add x y
  map_smul' := by
    intro r x
    ext s
    exact (semigroup s).map_smul r x

@[simp] theorem linearSemigroupOrbitLift_apply
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (semigroup : NNReal → E →ₗ[ℝ] E)
    (x : E) (s : NNReal) :
    linearSemigroupOrbitLift semigroup x s = semigroup s x :=
  rfl

/-- Time-zero conditioning on forward orbit paths. -/
def linearSemigroupOrbitCondition
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E] :
    LinearSemigroupOrbitSpace E →ₗ[ℝ] E where
  toFun := fun F => F 0
  map_add' := by
    intro F G
    rfl
  map_smul' := by
    intro r F
    rfl

@[simp] theorem linearSemigroupOrbitCondition_apply
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (F : LinearSemigroupOrbitSpace E) :
    linearSemigroupOrbitCondition F = F 0 :=
  rfl

/-- Forward translation of orbit paths. -/
def linearSemigroupOrbitTranslate
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (t : NNReal) :
    LinearSemigroupOrbitSpace E →ₗ[ℝ] LinearSemigroupOrbitSpace E where
  toFun := fun F s => F (s + t)
  map_add' := by
    intro F G
    rfl
  map_smul' := by
    intro r F
    rfl

@[simp] theorem linearSemigroupOrbitTranslate_apply
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (t s : NNReal)
    (F : LinearSemigroupOrbitSpace E) :
    linearSemigroupOrbitTranslate t F s = F (s + t) :=
  rfl

/-- Every real-linear semigroup with the correct value at time zero has a
canonical Markov compression on its forward-orbit path space. -/
noncomputable def linearSemigroupOrbitMarkovCompression
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (semigroup : NNReal → E →ₗ[ℝ] E)
    (semigroup_zero : ∀ x, semigroup 0 x = x) :
    LinearMarkovCompression
      E
      (LinearSemigroupOrbitSpace E)
      (fun t F => linearSemigroupOrbitTranslate t F)
      (fun t x => semigroup t x) where
  lift := linearSemigroupOrbitLift semigroup
  condition := linearSemigroupOrbitCondition
  condition_lift := by
    intro x
    simpa [linearSemigroupOrbitLift, linearSemigroupOrbitCondition] using
      semigroup_zero x
  condition_translate_lift := by
    intro t x
    simp [linearSemigroupOrbitLift, linearSemigroupOrbitCondition,
      linearSemigroupOrbitTranslate]

@[simp] theorem linearSemigroupOrbitMarkovCompression_lift_apply
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (semigroup : NNReal → E →ₗ[ℝ] E)
    (semigroup_zero : ∀ x, semigroup 0 x = x)
    (x : E) (s : NNReal) :
    (linearSemigroupOrbitMarkovCompression semigroup semigroup_zero).lift x s =
      semigroup s x :=
  rfl

@[simp] theorem linearSemigroupOrbitMarkovCompression_condition_apply
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (semigroup : NNReal → E →ₗ[ℝ] E)
    (semigroup_zero : ∀ x, semigroup 0 x = x)
    (F : LinearSemigroupOrbitSpace E) :
    (linearSemigroupOrbitMarkovCompression semigroup semigroup_zero).condition F =
      F 0 :=
  rfl

end

end MathlibAnalytic
end MGAP4D
