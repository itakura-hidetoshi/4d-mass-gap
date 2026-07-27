import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A linear Markov compression of a translated observable space onto a state
space.

`lift` embeds time-zero observables into a larger positive-time observable
space. `condition` is the time-zero conditional expectation. The two equations
record the retraction property and the Markov property after translation. No
topology, measure, or positivity is needed for this algebraic layer. -/
structure LinearMarkovCompression
    (E A : Type*)
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid A] [Module ℝ A]
    (translate : NNReal → A → A)
    (semigroup : NNReal → E → E) where
  lift : E →ₗ[ℝ] A
  condition : A →ₗ[ℝ] E
  condition_lift : ∀ x, condition (lift x) = x
  condition_translate_lift : ∀ t x,
    condition (translate t (lift x)) = semigroup t x

namespace LinearMarkovCompression

variable
    {E A : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid A] [Module ℝ A]
    {translate : NNReal → A → A}
    {semigroup : NNReal → E → E}

/-- If a represented state factors through the time-zero conditional
expectation, then the lifted time-zero observable represents the original
state. -/
theorem state_lift_eq
    (K : LinearMarkovCompression E A translate semigroup)
    {H : Type*}
    (state : A → H)
    (embed : E → H)
    (state_eq_embed_condition : ∀ a, state a = embed (K.condition a))
    (x : E) :
    state (K.lift x) = embed x := by
  rw [state_eq_embed_condition, K.condition_lift]

/-- The Markov compression identity turns translated lifted observables into
exact semigroup-evolved represented states. -/
theorem state_translate_lift_eq
    (K : LinearMarkovCompression E A translate semigroup)
    {H : Type*}
    (state : A → H)
    (embed : E → H)
    (state_eq_embed_condition : ∀ a, state a = embed (K.condition a))
    (t : NNReal) (x : E) :
    state (translate t (K.lift x)) = embed (semigroup t x) := by
  rw [state_eq_embed_condition, K.condition_translate_lift]

end LinearMarkovCompression

end

end MathlibAnalytic
end MGAP4D
