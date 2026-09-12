import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeOSGram
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- A finite path centered at time zero, represented by a reflected future, the
shared time-zero boundary state, and a positive-time future. -/
structure LinearMarkovCenteredFinitePath
    (Ω : Type*) (n : ℕ) where
  negative : LinearMarkovPositiveTimeFuturePath Ω n
  boundary : Ω
  positive : LinearMarkovPositiveTimeFuturePath Ω n
  deriving Fintype

/-- Conditional centered path law given the time-zero boundary state.  The two
finite futures are independent copies of the same conditional Markov future. -/
def linearMarkovCenteredFinitePathConditionalPMF
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω) :
    PMF (LinearMarkovCenteredFinitePath Ω n) :=
  (linearMarkovPositiveTimeFuturePMF transition n boundary).bind fun negative =>
    (linearMarkovPositiveTimeFuturePMF transition n boundary).map fun positive =>
      ⟨negative, boundary, positive⟩

/-- The finite centered path law obtained by first sampling the time-zero state
and then two conditionally independent finite futures. -/
def linearMarkovCenteredFinitePathPMF
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    PMF (LinearMarkovCenteredFinitePath Ω n) :=
  initial.bind fun boundary =>
    linearMarkovCenteredFinitePathConditionalPMF transition n boundary

/-- Finite time reflection swaps the negative and positive futures while fixing
the time-zero boundary state. -/
def linearMarkovCenteredFinitePathReflection
    {Ω : Type*} {n : ℕ}
    (path : LinearMarkovCenteredFinitePath Ω n) :
    LinearMarkovCenteredFinitePath Ω n :=
  ⟨path.positive, path.boundary, path.negative⟩

/-- Centered finite time reflection is involutive. -/
theorem linearMarkovCenteredFinitePathReflection_involutive
    {Ω : Type*} {n : ℕ} :
    Function.Involutive
      (@linearMarkovCenteredFinitePathReflection Ω n) := by
  rintro ⟨negative, boundary, positive⟩
  rfl

/-- Lift a finite-future observable to the positive-time half of a centered
finite path. -/
def linearMarkovCenteredFinitePathPositiveLift
    {Ω : Type*} {n : ℕ}
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (path : LinearMarkovCenteredFinitePath Ω n) : ℝ :=
  F path.positive

/-- Reflection sends a positive-time lift to the reflected finite future. -/
@[simp] theorem linearMarkovCenteredFinitePathPositiveLift_reflection
    {Ω : Type*} {n : ℕ}
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ)
    (path : LinearMarkovCenteredFinitePath Ω n) :
    linearMarkovCenteredFinitePathPositiveLift F
        (linearMarkovCenteredFinitePathReflection path) =
      F path.negative := by
  rfl

/-- The conditional centered law is invariant under finite time reflection. -/
theorem linearMarkovCenteredFinitePathConditionalPMF_map_reflection
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω) :
    (linearMarkovCenteredFinitePathConditionalPMF transition n boundary).map
        linearMarkovCenteredFinitePathReflection =
      linearMarkovCenteredFinitePathConditionalPMF transition n boundary := by
  let q := linearMarkovPositiveTimeFuturePMF transition n boundary
  unfold linearMarkovCenteredFinitePathConditionalPMF
  rw [PMF.map_bind]
  simp only [PMF.map_comp]
  simpa [q, PMF.map, Function.comp_def,
    linearMarkovCenteredFinitePathReflection] using
    (PMF.bind_comm q q
      (fun negative positive =>
        PMF.pure
          (⟨positive, boundary, negative⟩ :
            LinearMarkovCenteredFinitePath Ω n)))

/-- The full finite centered path law is invariant under time reflection. -/
theorem linearMarkovCenteredFinitePathPMF_map_reflection
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovCenteredFinitePathPMF initial transition n).map
        linearMarkovCenteredFinitePathReflection =
      linearMarkovCenteredFinitePathPMF initial transition n := by
  unfold linearMarkovCenteredFinitePathPMF
  rw [PMF.map_bind]
  apply congrArg (PMF.bind initial)
  funext boundary
  exact linearMarkovCenteredFinitePathConditionalPMF_map_reflection
    transition n boundary

/-- Reflection invariance of the finite centered law in real-expectation form. -/
theorem linearMarkovCenteredFinitePathPMF_expectation_reflection
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (H : LinearMarkovCenteredFinitePath Ω n → ℝ) :
    finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n)
        (H ∘ linearMarkovCenteredFinitePathReflection) =
      finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n) H := by
  calc
    finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n)
        (H ∘ linearMarkovCenteredFinitePathReflection) =
      finitePMFExpectationReal
        ((linearMarkovCenteredFinitePathPMF initial transition n).map
          linearMarkovCenteredFinitePathReflection) H := by
            symm
            exact finite_pmfExpectationReal_map
              (linearMarkovCenteredFinitePathPMF initial transition n)
              linearMarkovCenteredFinitePathReflection H
    _ = finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n) H := by
          rw [linearMarkovCenteredFinitePathPMF_map_reflection]

/-- Under a fixed boundary, the reflected/positive product expectation factors
as the product of the two conditional future amplitudes. -/
theorem linearMarkovCenteredFinitePathConditionalPMF_reflectedProduct_expectation
    {Ω : Type*} [Fintype Ω]
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (boundary : Ω)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    finitePMFExpectationReal
        (linearMarkovCenteredFinitePathConditionalPMF transition n boundary)
        (fun path => F path.negative * G path.positive) =
      linearMarkovPositiveTimeBoundaryAmplitude transition n F boundary *
        linearMarkovPositiveTimeBoundaryAmplitude transition n G boundary := by
  let q := linearMarkovPositiveTimeFuturePMF transition n boundary
  unfold linearMarkovCenteredFinitePathConditionalPMF
  rw [finite_pmfExpectationReal_bind]
  simp_rw [finite_pmfExpectationReal_map]
  simp_rw [finite_pmfExpectationReal_const_mul]
  have hcomm :
      (fun negative =>
        F negative * finitePMFExpectationReal q G) =
        fun negative =>
          finitePMFExpectationReal q G * F negative := by
    funext negative
    ring
  rw [hcomm, finite_pmfExpectationReal_const_mul]
  rw [linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation,
    linearMarkovPositiveTimeBoundaryAmplitude_eq_expectation]
  ring

/-- The previously constructed doubled-future OS bilinear form is exactly the
expectation of a reflected positive-time observable times an unreflected one
under the honest finite centered path PMF. -/
theorem linearMarkovCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (linearMarkovCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift G path) =
      linearMarkovPositiveTimeOSForm initial transition n F G := by
  rw [linearMarkovPositiveTimeOSForm_eq_boundaryPairing]
  unfold linearMarkovCenteredFinitePathPMF
  rw [finite_pmfExpectationReal_bind]
  calc
    finitePMFExpectationReal initial
        (fun boundary =>
          finitePMFExpectationReal
            (linearMarkovCenteredFinitePathConditionalPMF transition n boundary)
            (fun path =>
              linearMarkovCenteredFinitePathPositiveLift F
                  (linearMarkovCenteredFinitePathReflection path) *
                linearMarkovCenteredFinitePathPositiveLift G path)) =
      finitePMFExpectationReal initial
        (fun boundary =>
          linearMarkovPositiveTimeBoundaryAmplitude transition n F boundary *
            linearMarkovPositiveTimeBoundaryAmplitude transition n G boundary) := by
              apply congrArg (finitePMFExpectationReal initial)
              funext boundary
              simpa [linearMarkovCenteredFinitePathPositiveLift] using
                linearMarkovCenteredFinitePathConditionalPMF_reflectedProduct_expectation
                  transition n boundary F G
    _ = ∑ boundary : Ω,
        (initial boundary).toReal *
          linearMarkovPositiveTimeBoundaryAmplitude transition n F boundary *
          linearMarkovPositiveTimeBoundaryAmplitude transition n G boundary := by
            unfold finitePMFExpectationReal
            apply Finset.sum_congr rfl
            intro boundary _hboundary
            ring

/-- In particular, the temporal OS quadratic form is the reflected square
expectation under the centered finite path law. -/
theorem linearMarkovCenteredFinitePathPMF_reflectedSquare_expectation_eq_OSForm
    {Ω : Type*} [Fintype Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (linearMarkovCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift F path) =
      linearMarkovPositiveTimeOSForm initial transition n F F :=
  linearMarkovCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    initial transition n F F

end

end MathlibAnalytic
end MGAP4D
