import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPositiveShiftKernelPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The Euclidean-time circumference of the even four-torus. -/
def finiteEvenFourTorusTimePeriod (H : ℕ) : ℕ :=
  (2 * H + 1) + 1

/-- One positive Euclidean-time step on the even four-torus vertex carrier. -/
def finiteEvenFourTorusVertexTimeTranslationEquiv
    (H : ℕ) : FiniteEvenFourTorusVertex H ≃ FiniteEvenFourTorusVertex H where
  toFun := fun v =>
    v + finiteFourTorusUnitStep (2 * H + 1) 0
  invFun := fun v =>
    v - finiteFourTorusUnitStep (2 * H + 1) 0
  left_inv := by
    intro v
    exact add_sub_cancel_right v
      (finiteFourTorusUnitStep (2 * H + 1) 0)
  right_inv := by
    intro v
    exact sub_add_cancel v
      (finiteFourTorusUnitStep (2 * H + 1) 0)

@[simp] theorem finiteEvenFourTorusVertexTimeTranslationEquiv_apply
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    finiteEvenFourTorusVertexTimeTranslationEquiv H v =
      finiteFourTorusStep (2 * H + 1) v 0 := by
  rfl

@[simp] theorem finiteEvenFourTorusVertexTimeTranslationEquiv_symm_apply
    (H : ℕ) (v : FiniteEvenFourTorusVertex H) :
    (finiteEvenFourTorusVertexTimeTranslationEquiv H).symm v =
      v - finiteFourTorusUnitStep (2 * H + 1) 0 := by
  rfl

/-- The induced endpoint-wise translation of directed edges. -/
def finiteEvenFourTorusEdgeTimeTranslationEquiv
    (H : ℕ) : FiniteEvenFourTorusEdge H ≃ FiniteEvenFourTorusEdge H where
  toFun := fun e =>
    (finiteEvenFourTorusVertexTimeTranslationEquiv H e.1,
      finiteEvenFourTorusVertexTimeTranslationEquiv H e.2)
  invFun := fun e =>
    ((finiteEvenFourTorusVertexTimeTranslationEquiv H).symm e.1,
      (finiteEvenFourTorusVertexTimeTranslationEquiv H).symm e.2)
  left_inv := by
    intro e
    rcases e with ⟨s, t⟩
    simp
  right_inv := by
    intro e
    rcases e with ⟨s, t⟩
    simp

@[simp] theorem finiteEvenFourTorusEdgeTimeTranslationEquiv_apply
    (H : ℕ) (e : FiniteEvenFourTorusEdge H) :
    finiteEvenFourTorusEdgeTimeTranslationEquiv H e =
      (finiteFourTorusStep (2 * H + 1) e.1 0,
        finiteFourTorusStep (2 * H + 1) e.2 0) := by
  rfl

/-- Translation of plaquettes by translating the base vertex and retaining the
ordered direction pair. -/
def finiteEvenFourTorusPlaquetteTimeTranslationEquiv
    (H : ℕ) :
    FiniteFourTorusPlaquette (2 * H + 1) ≃
      FiniteFourTorusPlaquette (2 * H + 1) where
  toFun := fun p =>
    (finiteEvenFourTorusVertexTimeTranslationEquiv H p.1, p.2)
  invFun := fun p =>
    ((finiteEvenFourTorusVertexTimeTranslationEquiv H).symm p.1, p.2)
  left_inv := by
    intro p
    rcases p with ⟨v, d⟩
    simp
  right_inv := by
    intro p
    rcases p with ⟨v, d⟩
    simp

/-- Pullback of a full edge configuration by one positive Euclidean-time step. -/
def finiteEvenFourTorusConfigurationTimeTranslationEquiv
    (H : ℕ) :
    FiniteEvenFourTorusConfiguration H ≃
      FiniteEvenFourTorusConfiguration H where
  toFun := fun A e =>
    A ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm e)
  invFun := fun A e =>
    A (finiteEvenFourTorusEdgeTimeTranslationEquiv H e)
  left_inv := by
    intro A
    funext e
    exact congrArg A
      ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm_apply_apply e)
  right_inv := by
    intro A
    funext e
    exact congrArg A
      ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).apply_symm_apply e)

/-- The actual positive-configuration permutation induced by geometric time
translation on the concrete even-torus edge carrier. -/
def finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv
    (H : ℕ) :
    (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration ≃
      (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration where
  toFun := fun x e =>
    x ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm e)
  invFun := fun x e =>
    x (finiteEvenFourTorusEdgeTimeTranslationEquiv H e)
  left_inv := by
    intro x
    funext e
    exact congrArg x
      ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm_apply_apply e)
  right_inv := by
    intro x
    funext e
    exact congrArg x
      ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).apply_symm_apply e)

/-- Iterating vertex time translation adds the corresponding natural-number
amount to the periodic time coordinate and leaves the spatial coordinates
unchanged. -/
theorem finiteEvenFourTorusVertexTimeTranslationEquiv_pow_apply
    (H n : ℕ) (v : FiniteEvenFourTorusVertex H) (i : Fin 4) :
    ((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) v i =
      v i + if i = 0 then
        (n : ZMod ((2 * H + 1) + 1))
      else 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ']
      change finiteEvenFourTorusVertexTimeTranslationEquiv H
          (((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) v) i = _
      rw [finiteEvenFourTorusVertexTimeTranslationEquiv_apply]
      by_cases hi : i = 0
      · subst i
        simp [finiteFourTorusStep, finiteFourTorusUnitStep,
          ih, Nat.cast_succ, add_assoc]
      · simp [finiteFourTorusStep, finiteFourTorusUnitStep, ih, hi]

/-- One-step vertex translation has exactly the torus time circumference as a
period. -/
theorem finiteEvenFourTorusVertexTimeTranslationEquiv_pow_period
    (H : ℕ) :
    (finiteEvenFourTorusVertexTimeTranslationEquiv H) ^
        finiteEvenFourTorusTimePeriod H = Equiv.refl _ := by
  apply Equiv.ext
  intro v
  funext i
  rw [finiteEvenFourTorusVertexTimeTranslationEquiv_pow_apply]
  by_cases hi : i = 0
  · subst i
    simp [finiteEvenFourTorusTimePeriod]
  · simp [hi]

/-- Powers of endpoint-wise edge translation are the endpoint-wise powers of
vertex translation. -/
theorem finiteEvenFourTorusEdgeTimeTranslationEquiv_pow_apply
    (H n : ℕ) (e : FiniteEvenFourTorusEdge H) :
    ((finiteEvenFourTorusEdgeTimeTranslationEquiv H) ^ n) e =
      (((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) e.1,
        ((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) e.2) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [pow_succ']
      change
        finiteEvenFourTorusEdgeTimeTranslationEquiv H
            (((finiteEvenFourTorusEdgeTimeTranslationEquiv H) ^ n) e) =
          (finiteEvenFourTorusVertexTimeTranslationEquiv H
              (((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) e.1),
            finiteEvenFourTorusVertexTimeTranslationEquiv H
              (((finiteEvenFourTorusVertexTimeTranslationEquiv H) ^ n) e.2))
      rw [ih]
      rfl

/-- Endpoint-wise edge translation has the same geometric period. -/
theorem finiteEvenFourTorusEdgeTimeTranslationEquiv_pow_period
    (H : ℕ) :
    (finiteEvenFourTorusEdgeTimeTranslationEquiv H) ^
        finiteEvenFourTorusTimePeriod H = Equiv.refl _ := by
  apply Equiv.ext
  intro e
  rw [finiteEvenFourTorusEdgeTimeTranslationEquiv_pow_apply,
    finiteEvenFourTorusVertexTimeTranslationEquiv_pow_period]
  rfl

/-- Powers of the positive-configuration pullback are pullback by the inverse
power of the geometric edge translation. -/
theorem finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv_pow_apply
    (H n : ℕ)
    (x : (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration)
    (e : FiniteEvenFourTorusEdge H) :
    (((finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H) ^ n) x) e =
      x ((((finiteEvenFourTorusEdgeTimeTranslationEquiv H) ^ n).symm) e) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [pow_succ']
      change
        (((finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H) ^ n) x)
            ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm e) =
          x ((((finiteEvenFourTorusEdgeTimeTranslationEquiv H) ^ n).symm)
            ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm e))
      exact ih ((finiteEvenFourTorusEdgeTimeTranslationEquiv H).symm e)

/-- Pullback along a finite-period edge translation has the same period on the
positive-configuration function space. -/
theorem finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv_pow_period
    (H : ℕ) :
    (finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv H) ^
        finiteEvenFourTorusTimePeriod H = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  funext e
  rw [finiteEvenFourTorusPositiveConfigurationTimeTranslationEquiv_pow_apply,
    finiteEvenFourTorusEdgeTimeTranslationEquiv_pow_period]
  rfl

end

end MathlibAnalytic
end MGAP4D
