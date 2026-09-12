import Mathlib

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Transport a linear observable realization through a linear equivalence and a
linear decoding map.

The intended application is a finite Gibbs Hilbert vector first converted back
to its underlying observable by division by `sqrt(mu)`, then realized as an
actual positive-time observable. -/
noncomputable def decodedObservableRealization
    {E G A O : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid G] [Module ℝ G]
    [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid O] [Module ℝ O]
    (e : E ≃ₗ[ℝ] G)
    (decode : G →ₗ[ℝ] A)
    (realize : A →ₗ[ℝ] O) : E →ₗ[ℝ] O :=
  realize.comp (decode.comp e.toLinearMap)

@[simp] theorem decodedObservableRealization_apply
    {E G A O : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid G] [Module ℝ G]
    [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid O] [Module ℝ O]
    (e : E ≃ₗ[ℝ] G)
    (decode : G →ₗ[ℝ] A)
    (realize : A →ₗ[ℝ] O)
    (x : E) :
    decodedObservableRealization e decode realize x =
      realize (decode (e x)) :=
  rfl

/-- If encoding after decoding is the identity and realized observables have the
expected represented state, the decoded realization represents every source
vector exactly.

No topology or continuity is needed at this algebraic layer. -/
theorem state_decodedObservableRealization_eq
    {E G A O H : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid G] [Module ℝ G]
    [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid O] [Module ℝ O]
    (e : E ≃ₗ[ℝ] G)
    (decode : G →ₗ[ℝ] A)
    (encode : A →ₗ[ℝ] G)
    (realize : A →ₗ[ℝ] O)
    (state : O → H)
    (embed : E → H)
    (hEncodeDecode : ∀ y : G, encode (decode y) = y)
    (hState : ∀ a : A,
      state (realize a) = embed (e.symm (encode a)))
    (x : E) :
    state (decodedObservableRealization e decode realize x) = embed x := by
  rw [decodedObservableRealization_apply, hState,
    hEncodeDecode, e.symm_apply_apply]

/-- Observable-level intertwining with a source evolution automatically yields
intertwining of represented states. -/
theorem state_translate_decodedObservableRealization_eq
    {E G A O H T : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid G] [Module ℝ G]
    [AddCommMonoid A] [Module ℝ A]
    [AddCommMonoid O] [Module ℝ O]
    (e : E ≃ₗ[ℝ] G)
    (decode : G →ₗ[ℝ] A)
    (encode : A →ₗ[ℝ] G)
    (realize : A →ₗ[ℝ] O)
    (state : O → H)
    (embed : E → H)
    (translate : T → O → O)
    (evolve : T → E → E)
    (hEncodeDecode : ∀ y : G, encode (decode y) = y)
    (hState : ∀ a : A,
      state (realize a) = embed (e.symm (encode a)))
    (hTranslate : ∀ t x,
      translate t (decodedObservableRealization e decode realize x) =
        decodedObservableRealization e decode realize (evolve t x))
    (t : T) (x : E) :
    state
        (translate t
          (decodedObservableRealization e decode realize x)) =
      embed (evolve t x) := by
  rw [hTranslate t x]
  exact state_decodedObservableRealization_eq
    e decode encode realize state embed hEncodeDecode hState (evolve t x)

end

end MathlibAnalytic
end MGAP4D
