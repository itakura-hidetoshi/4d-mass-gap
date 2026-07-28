import MGAP4D.MathlibAnalytic.LinearMarkovPositiveTimeCylinderFiniteRepresentation
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerCenteredRestriction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Restrict a two-sided integer-time path to its nonnegative-time half. -/
def linearMarkovIntegerPathNonnegativeRestriction
    (path : ℤ → Ω) : ℕ → Ω :=
  fun t => path (t : ℤ)

@[simp] theorem linearMarkovIntegerPathNonnegativeRestriction_apply
    (path : ℤ → Ω) (t : ℕ) :
    linearMarkovIntegerPathNonnegativeRestriction path t = path (t : ℤ) :=
  rfl

/-- The positive future unpacked from a centered full-path restriction is exactly
the strictly-positive prefix of the original path. -/
theorem linearMarkovChronologicalToCentered_centeredRestriction_positive
    (n : ℕ) (path : ℤ → Ω) :
    (linearMarkovChronologicalToCenteredFinitePath
      (linearMarkovIntegerCenteredPathRestriction n path)).positive =
      linearMarkovPositiveTimeFuturePrefix n
        (linearMarkovIntegerPathNonnegativeRestriction path) := by
  funext i
  have hi := i.2
  unfold linearMarkovChronologicalToCenteredFinitePath
    linearMarkovChronologicalExplicitToSum
    linearMarkovChronologicalSumToCenteredFinitePath
    linearMarkovSingleChainCenteredFinitePath
    linearMarkovIntegerCenteredPathRestriction
    linearMarkovPositiveTimeFuturePrefix
    linearMarkovIntegerPathNonnegativeRestriction
    linearMarkovIntegerCenteredTime
  simp
  apply congrArg path
  omega

/-- The boundary unpacked from a centered full-path restriction is the time-zero
coordinate. -/
theorem linearMarkovChronologicalToCentered_centeredRestriction_boundary
    (n : ℕ) (path : ℤ → Ω) :
    (linearMarkovChronologicalToCenteredFinitePath
      (linearMarkovIntegerCenteredPathRestriction n path)).boundary = path 0 := by
  unfold linearMarkovChronologicalToCenteredFinitePath
    linearMarkovChronologicalExplicitToSum
    linearMarkovChronologicalSumToCenteredFinitePath
    linearMarkovSingleChainCenteredFinitePath
    linearMarkovIntegerCenteredPathRestriction
    linearMarkovIntegerCenteredTime
  simp

/-- The reflected past unpacked from a centered full-path restriction is exactly
the strictly-positive prefix of the globally reflected path. -/
theorem linearMarkovChronologicalToCentered_centeredRestriction_negative
    (n : ℕ) (path : ℤ → Ω) :
    (linearMarkovChronologicalToCenteredFinitePath
      (linearMarkovIntegerCenteredPathRestriction n path)).negative =
      linearMarkovPositiveTimeFuturePrefix n
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path)) := by
  funext i
  have hi := i.2
  have hin : i.1 ≤ n := Nat.le_of_lt_succ i.2
  unfold linearMarkovChronologicalToCenteredFinitePath
    linearMarkovChronologicalExplicitToSum
    linearMarkovChronologicalSumToCenteredFinitePath
    linearMarkovSingleChainCenteredFinitePath
    linearMarkovSingleChainReflectedPast
    linearMarkovFinitePathReverse
    linearMarkovIntegerCenteredPathRestriction
    linearMarkovPositiveTimeFuturePrefix
    linearMarkovIntegerPathNonnegativeRestriction
    linearMarkovIntegerPathReflection
    linearMarkovIntegerCenteredTime
  simp
  apply congrArg path
  omega

/-- The full-path reflected product of finite future observables is exactly the
existing finite temporal Osterwalder--Schrader form. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_finite_reflectedProduct_integral_eq_OSForm
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    (∫ path,
        F (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction
            (linearMarkovIntegerPathReflection path))) *
        G (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb) =
      linearMarkovPositiveTimeOSForm initial transition n F G := by
  let Q : LinearMarkovCenteredFinitePath Ω n → ℝ :=
    fun centered => F centered.negative * G centered.positive
  let K : LinearMarkovIntegerCenteredFinitePath Ω n → ℝ :=
    fun chronological => Q
      (linearMarkovChronologicalToCenteredFinitePath chronological)
  have hpoint : ∀ path : ℤ → Ω,
      F (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction
            (linearMarkovIntegerPathReflection path))) *
        G (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction path)) =
      K (linearMarkovIntegerCenteredPathRestriction n path) := by
    intro path
    unfold K Q
    rw [linearMarkovChronologicalToCentered_centeredRestriction_negative]
    rw [linearMarkovChronologicalToCentered_centeredRestriction_positive]
  calc
    (∫ path,
        F (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction
            (linearMarkovIntegerPathReflection path))) *
        G (linearMarkovPositiveTimeFuturePrefix n
          (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb) =
      ∫ path, K (linearMarkovIntegerCenteredPathRestriction n path)
        ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = finitePMFExpectationReal
        (linearMarkovIntegerCenteredFinitePathPMF initial transition n) K :=
      linearMarkovTwoSidedIntegerPathMeasure_integral_centeredRestriction
        initial transition hdb n K
    _ = finitePMFExpectationReal
        ((linearMarkovIntegerCenteredFinitePathPMF initial transition n).map
          linearMarkovChronologicalToCenteredFinitePath) Q := by
          symm
          simpa [K] using
            finite_pmfExpectationReal_map
              (linearMarkovIntegerCenteredFinitePathPMF initial transition n)
              linearMarkovChronologicalToCenteredFinitePath Q
    _ = finitePMFExpectationReal
        (linearMarkovCenteredFinitePathPMF initial transition n) Q := by
          rw [linearMarkovChronologicalCenteredFinitePathPMF_map_unpack_eq_centered
            initial transition hdb n]
    _ = linearMarkovPositiveTimeOSForm initial transition n F G := by
          simpa [Q, linearMarkovCenteredFinitePathPositiveLift] using
            linearMarkovCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
              initial transition n F G

/-- Reflection positivity for every finite strictly-positive-time future
observable on the full two-sided path measure. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_finite_reflection_nonneg
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath Ω n → ℝ) :
    0 ≤ ∫ path,
      F (linearMarkovPositiveTimeFuturePrefix n
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path))) *
      F (linearMarkovPositiveTimeFuturePrefix n
        (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  rw [linearMarkovTwoSidedIntegerPathMeasure_finite_reflectedProduct_integral_eq_OSForm]
  exact linearMarkovPositiveTimeOSForm_nonneg initial transition n F

/-- Temporal Osterwalder--Schrader reflection positivity on the complete generated
positive-time cylinder algebra of the two-sided detailed-balanced path law. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_positiveTime_reflection_nonneg
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    0 ≤ ∫ path,
      ((F : (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path))) *
      ((F : (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction path))
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  rcases linearMarkovPositiveTimeCylinder_finiteRepresentable F with
    ⟨n, H, hF⟩
  rw [hF]
  simp only [Function.comp_apply]
  exact linearMarkovTwoSidedIntegerPathMeasure_finite_reflection_nonneg
    initial transition hdb n H

end

end MathlibAnalytic
end MGAP4D
