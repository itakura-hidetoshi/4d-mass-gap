import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathNatShiftInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Invariance under a nonpositive integer-time translation follows from
invariance under the inverse nonnegative shift. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_negNatShift
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (d : ℕ) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ))) =
      linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  let μ := linearMarkovTwoSidedIntegerPathMeasure initial transition hdb
  have hpos :
      μ.map (linearMarkovIntegerPathShift ((d : ℕ) : ℤ)) = μ :=
    linearMarkovTwoSidedIntegerPathMeasure_map_natShift
      initial transition hdb d
  have hposMeas : Measurable
      (linearMarkovIntegerPathShift ((d : ℕ) : ℤ) :
        (ℤ → Ω) → (ℤ → Ω)) :=
    linearMarkovIntegerPathShift_measurable _
  have hnegMeas : Measurable
      (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ)) :
        (ℤ → Ω) → (ℤ → Ω)) :=
    linearMarkovIntegerPathShift_measurable _
  change μ.map (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ))) = μ
  calc
    μ.map (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ))) =
      (μ.map (linearMarkovIntegerPathShift ((d : ℕ) : ℤ))).map
        (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ))) := by
          rw [hpos]
    _ = μ.map
        (linearMarkovIntegerPathShift (-((d : ℕ) : ℤ)) ∘
          linearMarkovIntegerPathShift ((d : ℕ) : ℤ)) :=
      Measure.map_map hnegMeas hposMeas
    _ = μ.map id := by
      apply congrArg (fun f => μ.map f)
      funext path
      exact linearMarkovIntegerPathShift_neg_left
        (((d : ℕ) : ℤ)) path
    _ = μ := by
      simpa using Measure.map_id μ

/-- The countably additive two-sided integer-time path law is invariant under
an arbitrary integer-time translation. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_shift
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (k : ℤ) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerPathShift k) =
      linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  cases k with
  | ofNat d =>
      exact linearMarkovTwoSidedIntegerPathMeasure_map_natShift
        initial transition hdb d
  | negSucc d =>
      have hk : Int.negSucc d = -(((d + 1 : ℕ) : ℤ)) := by
        omega
      rw [hk]
      exact linearMarkovTwoSidedIntegerPathMeasure_map_negNatShift
        initial transition hdb (d + 1)

end

end MathlibAnalytic
end MGAP4D
