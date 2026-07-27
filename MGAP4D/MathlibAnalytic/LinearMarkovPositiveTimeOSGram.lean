import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeCylinderAlgebra
import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathCylinderMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite strictly-positive-time future path with coordinates `1, ..., n + 1`.
The boundary state at time zero is kept separate. -/
abbrev LinearMarkovPositiveTimeFuturePath
    (Ω : Type*) (n : ℕ) :=
  Fin (n + 1) → Ω

/-- The conditional law of the strictly-positive-time future
`(X₁, ..., Xₙ₊₁)` given the time-zero boundary state `X₀ = boundary`. -/
def linearMarkovPositiveTimeFuturePMF
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω) :
    PMF (LinearMarkovPositiveTimeFuturePath Ω n) :=
  linearMarkovFinitePathPMF (transition boundary) transition n

/-- Real conditional probability of a finite positive-time future path. -/
def linearMarkovPositiveTimeFutureProbabilityReal
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω)
    (future : LinearMarkovPositiveTimeFuturePath Ω n) : ℝ :=
  (linearMarkovPositiveTimeFuturePMF transition n boundary future).toReal

/-- Conditional future amplitude of a finite future observable given the time-zero
boundary state.  The observable-first order agrees directly with the Gram
feature convention used below. -/
def linearMarkovPositiveTimeBoundaryAmplitude
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (boundary : Ω) : ℝ :=
  ∑ future : LinearMarkovPositiveTimeFuturePath Ω n,
    F future *
      linearMarkovPositiveTimeFutureProbabilityReal transition n boundary future

/-- The boundary amplitude is ordinary finite-PMF expectation under the
conditional future law. -/
theorem linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (boundary : Ω) :
    linearMarkovPositiveTimeBoundaryAmplitude transition n F boundary =
      finitePMFExpectationReal
        (linearMarkovPositiveTimeFuturePMF transition n boundary) F := by
  classical
  unfold linearMarkovPositiveTimeBoundaryAmplitude
    linearMarkovPositiveTimeFutureProbabilityReal
    finitePMFExpectationReal
  apply Finset.sum_congr rfl
  intro future _hfuture
  ring

/-- Time reflection on a pair of conditionally independent positive-time
futures.  The first component represents the reflected copy and the second the
positive-time copy. -/
def linearMarkovPositiveTimeFuturePairReflection
    {α : Type*} (pair : α × α) : α × α :=
  (pair.2, pair.1)

/-- The doubled-future time reflection is involutive. -/
theorem linearMarkovPositiveTimeFuturePairReflection_involutive
    {α : Type*} :
    Function.Involutive (@linearMarkovPositiveTimeFuturePairReflection α) := by
  rintro ⟨left, right⟩
  rfl

/-- Lift a positive-time future observable to the positive component of the
doubled future. -/
def linearMarkovPositiveTimeFuturePositiveLift
    {α : Type*} (F : α → ℝ) (pair : α × α) : ℝ :=
  F pair.2

/-- Reflection turns a positive-component observable into the corresponding
observable of the reflected component. -/
@[simp] theorem linearMarkovPositiveTimeFuturePositiveLift_reflection
    {α : Type*} (F : α → ℝ) (pair : α × α) :
    linearMarkovPositiveTimeFuturePositiveLift F
        (linearMarkovPositiveTimeFuturePairReflection pair) =
      F pair.1 := by
  rfl

/-- The boundary-conditioned doubled-future kernel.  It is the Gram kernel
obtained by taking two conditionally independent futures sharing the same
boundary state. -/
def linearMarkovPositiveTimeOSKernel
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (left right : LinearMarkovPositiveTimeFuturePath Ω n) : ℝ :=
  ∑ boundary : Ω,
    (initial boundary).toReal *
      linearMarkovPositiveTimeFutureProbabilityReal transition n boundary left *
      linearMarkovPositiveTimeFutureProbabilityReal transition n boundary right

/-- The doubled-future OS kernel is symmetric under time reflection. -/
theorem linearMarkovPositiveTimeOSKernel_symmetric
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (left right : LinearMarkovPositiveTimeFuturePath Ω n) :
    linearMarkovPositiveTimeOSKernel initial transition n left right =
      linearMarkovPositiveTimeOSKernel initial transition n right left := by
  classical
  unfold linearMarkovPositiveTimeOSKernel
  apply Finset.sum_congr rfl
  intro boundary _hboundary
  ring

/-- The finite doubled-future Osterwalder--Schrader bilinear form.  The factor
`F left` is the reflected positive-time observable and `G right` is the
unreflected positive-time observable. -/
def linearMarkovPositiveTimeOSForm
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) : ℝ :=
  ∑ left : LinearMarkovPositiveTimeFuturePath Ω n,
    ∑ right : LinearMarkovPositiveTimeFuturePath Ω n,
      F left * linearMarkovPositiveTimeOSKernel initial transition n left right *
        G right

/-- Audit-visible expression of the OS form as reflection of the first
positive-time observable followed by multiplication with the second. -/
theorem linearMarkovPositiveTimeOSForm_eq_reflected_kernel_expectation
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n F G =
      ∑ left : LinearMarkovPositiveTimeFuturePath Ω n,
        ∑ right : LinearMarkovPositiveTimeFuturePath Ω n,
          linearMarkovPositiveTimeFuturePositiveLift F
              (linearMarkovPositiveTimeFuturePairReflection (left, right)) *
            linearMarkovPositiveTimeOSKernel initial transition n left right *
            linearMarkovPositiveTimeFuturePositiveLift G (left, right) := by
  rfl

/-- Finite Gram bilinear identity with possibly distinct observables in the two
slots. -/
theorem finite_gram_bilinear_identity
    {α κ : Type*} [Fintype α] [Fintype κ]
    (coefficient : κ → ℝ)
    (feature : κ → α → ℝ)
    (F G : α → ℝ) :
    (∑ left : α, ∑ right : α,
      F left *
        (∑ boundary : κ,
          coefficient boundary * feature boundary left * feature boundary right) *
        G right) =
      ∑ boundary : κ,
        coefficient boundary *
          (∑ left : α, F left * feature boundary left) *
          (∑ right : α, G right * feature boundary right) := by
  classical
  calc
    (∑ left : α, ∑ right : α,
      F left *
        (∑ boundary : κ,
          coefficient boundary * feature boundary left * feature boundary right) *
        G right) =
        ∑ left : α, ∑ right : α, ∑ boundary : κ,
          coefficient boundary * (F left * feature boundary left) *
            (G right * feature boundary right) := by
              apply Finset.sum_congr rfl
              intro left _hleft
              apply Finset.sum_congr rfl
              intro right _hright
              rw [Finset.mul_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro boundary _hboundary
              ring
    _ = ∑ left : α, ∑ boundary : κ, ∑ right : α,
          coefficient boundary * (F left * feature boundary left) *
            (G right * feature boundary right) := by
              apply Finset.sum_congr rfl
              intro left _hleft
              rw [Finset.sum_comm]
    _ = ∑ boundary : κ, ∑ left : α, ∑ right : α,
          coefficient boundary * (F left * feature boundary left) *
            (G right * feature boundary right) := by
              rw [Finset.sum_comm]
    _ = ∑ boundary : κ,
        coefficient boundary *
          (∑ left : α, F left * feature boundary left) *
          (∑ right : α, G right * feature boundary right) := by
            apply Finset.sum_congr rfl
            intro boundary _hboundary
            calc
              (∑ left : α, ∑ right : α,
                coefficient boundary * (F left * feature boundary left) *
                  (G right * feature boundary right)) =
                  ∑ left : α,
                    (coefficient boundary * (F left * feature boundary left)) *
                      (∑ right : α, G right * feature boundary right) := by
                        apply Finset.sum_congr rfl
                        intro left _hleft
                        rw [← Finset.mul_sum]
              _ = (∑ left : α,
                    coefficient boundary * (F left * feature boundary left)) *
                    (∑ right : α, G right * feature boundary right) := by
                      rw [← Finset.sum_mul]
              _ = (coefficient boundary *
                    (∑ left : α, F left * feature boundary left)) *
                    (∑ right : α, G right * feature boundary right) := by
                      rw [← Finset.mul_sum]

/-- The reflected doubled-future OS form is exactly the boundary Gram pairing of
conditional future amplitudes. -/
theorem linearMarkovPositiveTimeOSForm_eq_boundaryPairing
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n F G =
      ∑ boundary : Ω,
        (initial boundary).toReal *
          linearMarkovPositiveTimeBoundaryAmplitude transition n F boundary *
          linearMarkovPositiveTimeBoundaryAmplitude transition n G boundary := by
  classical
  simpa [linearMarkovPositiveTimeOSForm,
    linearMarkovPositiveTimeOSKernel,
    linearMarkovPositiveTimeBoundaryAmplitude] using
    finite_gram_bilinear_identity
      (fun boundary : Ω => (initial boundary).toReal)
      (fun boundary future =>
        linearMarkovPositiveTimeFutureProbabilityReal
          transition n boundary future)
      F G

/-- The doubled-future OS bilinear form is symmetric. -/
theorem linearMarkovPositiveTimeOSForm_symmetric
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n F G =
      linearMarkovPositiveTimeOSForm initial transition n G F := by
  rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing,
    linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
  apply Finset.sum_congr rfl
  intro boundary _hboundary
  ring

/-- Reflection positivity of the finite doubled-future Markov kernel. -/
theorem linearMarkovPositiveTimeOSForm_nonneg
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    0 ≤ linearMarkovPositiveTimeOSForm initial transition n F F := by
  rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
  exact Finset.sum_nonneg fun boundary _hboundary => by
    have hterm :
        0 ≤ (initial boundary).toReal *
          (linearMarkovPositiveTimeBoundaryAmplitude
            transition n F boundary) ^ 2 :=
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    simpa [pow_two, mul_assoc] using hterm

/-- A positive-time product cylinder on the infinite path is represented by the
same finite product evaluated on the future prefix after one left shift. -/
theorem linearMarkovPositiveTimePathProduct_eq_finiteFuturePrefix
    {Ω : Type*}
    {n : ℕ}
    (fs : Fin (n + 1) → Ω → ℝ)
    (path : ℕ → Ω) :
    linearMarkovPositiveTimePathProduct fs path =
      linearMarkovFinitePathProduct fs
        (linearMarkovInfinitePathFinPrefix n
          (linearMarkovPathShift path)) := by
  simp [linearMarkovPositiveTimePathProduct,
    linearMarkovPositiveTimeCoordinate,
    linearMarkovFinitePathProduct,
    linearMarkovInfinitePathFinPrefix,
    linearMarkovPathShift]

/-- The conditional boundary amplitude of a positive-time product cylinder is
exactly the existing backward Markov cylinder moment started from the one-step
boundary transition law. -/
theorem linearMarkovPositiveTimeBoundaryAmplitude_product_eq_cylinderMoment
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ)
    (boundary : Ω) :
    linearMarkovPositiveTimeBoundaryAmplitude transition n
        (linearMarkovFinitePathProduct fs) boundary =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal (transition boundary))
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) := by
  rw [linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation]
  exact linearMarkovFinitePathPMF_product_expectation_eq_cylinderMoment
    (transition boundary) transition n fs

/-- The OS quadratic form of a positive-time product cylinder is the initial
expectation of the square of its conditional boundary cylinder moment. -/
theorem linearMarkovPositiveTimeOSForm_product_eq_boundaryMoment_sq
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    linearMarkovPositiveTimeOSForm initial transition n
        (linearMarkovFinitePathProduct fs)
        (linearMarkovFinitePathProduct fs) =
      ∑ boundary : Ω,
        (initial boundary).toReal *
          (linearMarkovCylinderMoment
            (finitePMFExpectationReal (transition boundary))
            (finitePMFTransitionExpectationLinearMap transition)
            (List.ofFn fs)) ^ 2 := by
  rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
  apply Finset.sum_congr rfl
  intro boundary _hboundary
  rw [linearMarkovPositiveTimeBoundaryAmplitude_product_eq_cylinderMoment]
  ring

end

end MathlibAnalytic
end MGAP4D
