import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertEvenTimePositive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Positivity of the stationary one-step transition quadratic form.  This is the
minimal extra input needed to upgrade symmetry of the temporal OS shift to
positivity at odd times. -/
def LinearMarkovTransitionQuadraticNonnegative
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) : Prop :=
  ∀ f : Ω → ℝ,
    0 ≤ finitePMFExpectationReal initial
      (fun boundary =>
        finitePMFExpectationReal (transition boundary) f * f boundary)

/-- Deleting the last coordinate of a longer conditional future does not change
the boundary amplitude of an observable that ignores that coordinate. -/
theorem linearMarkovPositiveTimeBoundaryAmplitude_init
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (H : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (boundary : Ω) :
    linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
        (H ∘ Fin.init) boundary =
      linearMarkovPositiveTimeBoundaryAmplitude transition n H boundary := by
  rw [linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation,
    linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation]
  calc
    finitePMFExpectationReal
        (linearMarkovPositiveTimeFuturePMF transition (n + 1) boundary)
        (H ∘ Fin.init) =
      finitePMFExpectationReal
        ((linearMarkovPositiveTimeFuturePMF transition (n + 1) boundary).map
          Fin.init) H := by
            symm
            exact finite_pmfExpectationReal_map
              (linearMarkovPositiveTimeFuturePMF transition (n + 1) boundary)
              Fin.init H
    _ = finitePMFExpectationReal
        (linearMarkovPositiveTimeFuturePMF transition n boundary) H := by
          unfold linearMarkovPositiveTimeFuturePMF
          rw [linearMarkovFinitePathPMF_succ_map_init]

/-- The time-one temporal OS quadratic form is a stationary transition quadratic
form of the finite boundary amplitude. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_shift_self_eq_transitionQuadratic
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    ∃ f : Ω → ℝ,
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
          (linearMarkovPositiveTimeShiftAlgHom F) F =
        finitePMFExpectationReal initial
          (fun boundary =>
            finitePMFExpectationReal (transition boundary) f * f boundary) := by
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable F with
    ⟨n, H, hF⟩
  let shiftedH : LinearMarkovPositiveTimeFuturePath Ω (n + 1) → ℝ :=
    H ∘ linearMarkovPositiveTimeFutureTail (Ω := Ω) n
  let unshiftedH : LinearMarkovPositiveTimeFuturePath Ω (n + 1) → ℝ :=
    H ∘ Fin.init
  let f : Ω → ℝ :=
    linearMarkovPositiveTimeBoundaryAmplitude transition n H
  have hshift :
      (((linearMarkovPositiveTimeShiftAlgHom F :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)) =
        shiftedH ∘ linearMarkovPositiveTimeFuturePrefix (n + 1) := by
    funext path
    change (F : (ℕ → Ω) → ℝ) (linearMarkovPathShift path) =
      H (linearMarkovPositiveTimeFutureTail (Ω := Ω) n
        (linearMarkovPositiveTimeFuturePrefix (n + 1) path))
    rw [congrFun hF (linearMarkovPathShift path)]
    rfl
  have hunshift :
      ((F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ) =
        unshiftedH ∘ linearMarkovPositiveTimeFuturePrefix (n + 1) := by
    funext path
    rw [congrFun hF path]
    rfl
  refine ⟨f, ?_⟩
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F) F =
      linearMarkovPositiveTimeOSForm initial transition (n + 1)
        shiftedH unshiftedH :=
      linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F) F
        (n + 1) shiftedH unshiftedH hshift hunshift
    _ = ∑ boundary : Ω,
        (initial boundary).toReal *
          linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
            shiftedH boundary *
          linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
            unshiftedH boundary := by
      rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
    _ = finitePMFExpectationReal initial
        (fun boundary =>
          finitePMFExpectationReal (transition boundary) f * f boundary) := by
      change
        (∑ boundary : Ω,
          (initial boundary).toReal *
            linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
              shiftedH boundary *
            linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
              unshiftedH boundary) =
          ∑ boundary : Ω,
            (initial boundary).toReal *
              (finitePMFExpectationReal (transition boundary) f * f boundary)
      apply Finset.sum_congr rfl
      intro boundary _hboundary
      rw [linearMarkovPositiveTimeBoundaryAmplitude_tail,
        linearMarkovPositiveTimeBoundaryAmplitude_init]
      dsimp only [f]
      ring

/-- A nonnegative stationary transition quadratic form makes the time-one OS
quadratic form nonnegative on cylinder observables. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_shift_self_nonneg
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (hquad : LinearMarkovTransitionQuadraticNonnegative initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    0 ≤ linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
      (linearMarkovPositiveTimeShiftAlgHom F) F := by
  rcases linearMarkovTwoSidedIntegerPathOSForm_shift_self_eq_transitionQuadratic
    initial transition hdb F with ⟨f, hf⟩
  rw [hf]
  exact hquad f

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

/-- Transition-quadratic positivity descends to the separated temporal OS
pre-Hilbert shift. -/
theorem inner_separatedShiftContinuousLinearMap_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (x : D.Separated) :
    0 ≤ inner ℝ (D.separatedShiftContinuousLinearMap x) x := by
  refine Quotient.inductionOn x ?_
  intro F
  change 0 ≤ inner ℝ
    (D.separatedShiftContinuousLinearMap (D.osClass F)) (D.osClass F)
  rw [D.separatedShiftContinuousLinearMap_apply,
    D.separatedShiftLinearMap_osClass,
    D.separated_inner_osClass_osClass]
  exact linearMarkovTwoSidedIntegerPathOSForm_shift_self_nonneg
    D.initial D.transition D.detailedBalance hquad F.observable

/-- Transition-quadratic positivity extends continuously to the completed
time-one temporal OS shift. -/
theorem inner_hilbertShiftContinuousLinearMap_self_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (x : D.Hilbert) :
    0 ≤ inner ℝ (D.hilbertShiftContinuousLinearMap x) x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_const (by fun_prop)) ?_
  intro y
  change 0 ≤ inner ℝ
    (D.hilbertShiftContinuousLinearMap (D.completedClass y))
    (D.completedClass y)
  rw [D.hilbertShiftContinuousLinearMap_completedClass,
    D.inner_completedClass_completedClass]
  exact D.inner_separatedShiftContinuousLinearMap_self_nonneg hquad y

/-- At every odd natural time, the temporal OS quadratic form is the time-one
quadratic form of the half-time translate. -/
theorem inner_hilbertShiftSemigroup_add_self_add_one_eq
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (n : ℕ)
    (x : D.Hilbert) :
    inner ℝ (D.hilbertShiftSemigroup (n + n + 1) x) x =
      inner ℝ
        (D.hilbertShiftContinuousLinearMap
          (D.hilbertShiftSemigroup n x))
        (D.hilbertShiftSemigroup n x) := by
  rw [show n + n + 1 = n + (n + 1) by omega,
    D.hilbertShiftSemigroup_add]
  change inner ℝ
      (D.hilbertShiftSemigroup n
        (D.hilbertShiftSemigroup (n + 1) x)) x = _
  rw [D.inner_hilbertShiftSemigroup_left_eq_right n]
  rw [D.hilbertShiftSemigroup_succ_apply]

/-- A nonnegative time-one transition quadratic form makes every odd-time member
of the temporal OS semigroup nonnegative. -/
theorem inner_hilbertShiftSemigroup_add_self_add_one_nonneg
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (hquad : LinearMarkovTransitionQuadraticNonnegative D.initial D.transition)
    (n : ℕ)
    (x : D.Hilbert) :
    0 ≤ inner ℝ (D.hilbertShiftSemigroup (n + n + 1) x) x := by
  rw [D.inner_hilbertShiftSemigroup_add_self_add_one_eq]
  exact D.inner_hilbertShiftContinuousLinearMap_self_nonneg hquad
    (D.hilbertShiftSemigroup n x)

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
