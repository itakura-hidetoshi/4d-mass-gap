import MGAP4D.MathlibAnalytic.FinitePMFRealExpectationJensen
import MGAP4D.MathlibAnalytic.LinearMarkovSingleChainCenteredTimeReflectionPMF
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSShiftQuotient
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Detailed balance implies one-step stationarity of real expectations. -/
theorem finitePMFExpectationReal_transition_stationary_of_detailedBalanceReal
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (f : Ω → ℝ) :
    finitePMFExpectationReal initial
        (fun x => finitePMFExpectationReal (transition x) f) =
      finitePMFExpectationReal initial f := by
  let pairLaw := linearMarkovPairPMF initial transition
  have hterminal : pairLaw.map Prod.snd = initial := by
    exact linearMarkovPairPMF_map_snd_of_detailedBalanceReal
      initial transition hdb
  calc
    finitePMFExpectationReal initial
        (fun x => finitePMFExpectationReal (transition x) f) =
      finitePMFExpectationReal pairLaw (fun xy => f xy.2) := by
        unfold pairLaw linearMarkovPairPMF
        rw [finite_pmfExpectationReal_bind]
        simp_rw [finite_pmfExpectationReal_map]
    _ = finitePMFExpectationReal (pairLaw.map Prod.snd) f := by
      rw [finite_pmfExpectationReal_map]
    _ = finitePMFExpectationReal initial f := by rw [hterminal]

/-- The transition expectation is an `L²(initial)` contraction under detailed
balance. -/
theorem finitePMFTransitionExpectation_sq_l2_le
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (f : Ω → ℝ) :
    finitePMFExpectationReal initial
        (fun x => (finitePMFExpectationReal (transition x) f) ^ 2) ≤
      finitePMFExpectationReal initial (fun x => (f x) ^ 2) := by
  calc
    finitePMFExpectationReal initial
        (fun x => (finitePMFExpectationReal (transition x) f) ^ 2) ≤
      finitePMFExpectationReal initial
        (fun x => finitePMFExpectationReal (transition x)
          (fun y => (f y) ^ 2)) := by
            apply finitePMFExpectationReal_mono
            intro x
            exact finitePMFExpectationReal_sq_le_expectation_sq
              (transition x) f
    _ = finitePMFExpectationReal initial (fun x => (f x) ^ 2) :=
      finitePMFExpectationReal_transition_stationary_of_detailedBalanceReal
        initial transition hdb (fun x => (f x) ^ 2)

/-- Delete the first strictly-positive coordinate from a longer finite future. -/
def linearMarkovPositiveTimeFutureTail
    (n : ℕ) :
    LinearMarkovPositiveTimeFuturePath Ω (n + 1) →
      LinearMarkovPositiveTimeFuturePath Ω n :=
  Fin.tail

/-- The tail of a longer positive-time prefix is the shorter prefix of the
one-step shifted path. -/
@[simp] theorem linearMarkovPositiveTimeFutureTail_prefix_shift
    (n : ℕ)
    (path : ℕ → Ω) :
    linearMarkovPositiveTimeFutureTail (Ω := Ω) n
        (linearMarkovPositiveTimeFuturePrefix (n + 1) path) =
      linearMarkovPositiveTimeFuturePrefix n
        (linearMarkovPathShift path) := by
  rfl

/-- The boundary amplitude of a translated finite-future observable is the
one-step transition expectation of its original boundary amplitude. -/
theorem linearMarkovPositiveTimeBoundaryAmplitude_tail
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (H : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (boundary : Ω) :
    linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
        (H ∘ linearMarkovPositiveTimeFutureTail (Ω := Ω) n) boundary =
      finitePMFExpectationReal (transition boundary)
        (linearMarkovPositiveTimeBoundaryAmplitude transition n H) := by
  rw [linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation]
  unfold linearMarkovPositiveTimeFuturePMF
  rw [linearMarkovFinitePathPMF_expectation_zero_tail]
  apply congrArg (finitePMFExpectationReal (transition boundary))
  funext next
  rw [linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation]
  apply congrArg
    (finitePMFExpectationReal
      (linearMarkovPositiveTimeFuturePMF transition n next))
  funext future
  rfl

/-- Boundary-amplitude squares contract after one positive-time translation. -/
theorem linearMarkovPositiveTimeBoundaryAmplitude_tail_sq_l2_le
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (H : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    finitePMFExpectationReal initial
        (fun boundary =>
          (linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
            (H ∘ linearMarkovPositiveTimeFutureTail (Ω := Ω) n)
            boundary) ^ 2) ≤
      finitePMFExpectationReal initial
        (fun boundary =>
          (linearMarkovPositiveTimeBoundaryAmplitude transition n H
            boundary) ^ 2) := by
  simpa only [linearMarkovPositiveTimeBoundaryAmplitude_tail] using
    finitePMFTransitionExpectation_sq_l2_le initial transition hdb
      (linearMarkovPositiveTimeBoundaryAmplitude transition n H)

/-- One positive-time translation is contractive for the full two-sided
integer-path Osterwalder--Schrader quadratic form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_shift_self_le_self
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F)
        (linearMarkovPositiveTimeShiftAlgHom F) ≤
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F := by
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable F with
    ⟨n, H, hF⟩
  let shiftedH : LinearMarkovPositiveTimeFuturePath Ω (n + 1) → ℝ :=
    H ∘ linearMarkovPositiveTimeFutureTail (Ω := Ω) n
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
  have hamp :=
    linearMarkovPositiveTimeBoundaryAmplitude_tail_sq_l2_le
      initial transition hdb n H
  calc
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F)
        (linearMarkovPositiveTimeShiftAlgHom F) =
      linearMarkovPositiveTimeOSForm initial transition (n + 1)
        shiftedH shiftedH :=
      linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
        initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F)
        (linearMarkovPositiveTimeShiftAlgHom F)
        (n + 1) shiftedH shiftedH hshift hshift
    _ = finitePMFExpectationReal initial
        (fun boundary =>
          (linearMarkovPositiveTimeBoundaryAmplitude transition (n + 1)
            shiftedH boundary) ^ 2) := by
      rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
      simp [finitePMFExpectationReal, pow_two, mul_assoc]
    _ ≤ finitePMFExpectationReal initial
        (fun boundary =>
          (linearMarkovPositiveTimeBoundaryAmplitude transition n H
            boundary) ^ 2) := by
      simpa [shiftedH] using hamp
    _ = linearMarkovPositiveTimeOSForm initial transition n H H := by
      rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
      simp [finitePMFExpectationReal, pow_two, mul_assoc]
    _ = linearMarkovTwoSidedIntegerPathOSForm initial transition hdb F F := by
      symm
      exact
        linearMarkovTwoSidedIntegerPathOSForm_eq_finite_of_commonRepresentation
          initial transition hdb F F n H H hF hF

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

/-- The descended temporal shift does not increase the separated OS norm. -/
theorem norm_separatedShiftLinearMap_le
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Separated) :
    ‖D.separatedShiftLinearMap x‖ ≤ ‖x‖ := by
  refine Quotient.inductionOn x ?_
  intro F
  have hform :=
    linearMarkovTwoSidedIntegerPathOSForm_shift_self_le_self
      D.initial D.transition D.detailedBalance F.observable
  have hinner :
      inner ℝ
          (D.separatedShiftLinearMap (D.osClass F))
          (D.separatedShiftLinearMap (D.osClass F)) ≤
        inner ℝ (D.osClass F) (D.osClass F) := by
    rw [D.separatedShiftLinearMap_osClass]
    rw [D.separated_inner_osClass_osClass,
      D.separated_inner_osClass_osClass]
    exact hform
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  exact (sq_le_sq₀
    (norm_nonneg (D.separatedShiftLinearMap (D.osClass F)))
    (norm_nonneg (D.osClass F))).mp hinner

/-- The contractive positive-time shift as a continuous real-linear endomorphism
of the separated temporal OS pre-Hilbert space. -/
noncomputable def separatedShiftContinuousLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Separated →L[ℝ] D.Separated :=
  D.separatedShiftLinearMap.mkContinuous 1 (by
    intro x
    simpa using D.norm_separatedShiftLinearMap_le x)

@[simp] theorem separatedShiftContinuousLinearMap_apply
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Separated) :
    D.separatedShiftContinuousLinearMap x = D.separatedShiftLinearMap x :=
  rfl

@[simp] theorem separatedShiftContinuousLinearMap_observableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    D.separatedShiftContinuousLinearMap (D.observableClass F) =
      D.observableClass (linearMarkovPositiveTimeShiftAlgHom F) := by
  exact D.separatedShiftLinearMap_observableClass F

/-- The continuous separated shift remains symmetric for the OS inner product. -/
theorem inner_separatedShiftContinuousLinearMap_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.Separated) :
    inner ℝ (D.separatedShiftContinuousLinearMap x) y =
      inner ℝ x (D.separatedShiftContinuousLinearMap y) := by
  exact D.inner_separatedShiftLinearMap_left_eq_right x y

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
