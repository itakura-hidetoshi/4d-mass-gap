import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalShift
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Reindexing the translated finite product back to the original finite time
set is measurable. -/
theorem linearMarkovIntegerFiniteSetNatShiftReindex_measurable
    (J : Finset ℤ) (d : ℕ) :
    Measurable
      (linearMarkovIntegerFiniteSetNatShiftReindex J d :
        (∀ _s : linearMarkovIntegerFiniteSetNatShift J d, Ω) →
          (∀ _t : J, Ω)) := by
  exact measurable_pi_lambda _ (fun t =>
    measurable_pi_apply
      (⟨t.1 + ((d : ℕ) : ℤ),
        linearMarkovIntegerFiniteSet_mem_natShift J d t⟩ :
          linearMarkovIntegerFiniteSetNatShift J d))

/-- Restricting a naturally shifted full path to `J` equals restricting the
original path to `J + d` and reindexing back to `J`. -/
theorem linearMarkovIntegerFiniteSetRestrict_natShift
    (J : Finset ℤ) (d : ℕ) :
    (J.restrict ∘
        (linearMarkovIntegerPathShift ((d : ℕ) : ℤ) :
          (ℤ → Ω) → (ℤ → Ω))) =
      linearMarkovIntegerFiniteSetNatShiftReindex J d ∘
        (linearMarkovIntegerFiniteSetNatShift J d).restrict := by
  funext path t
  rfl

/-- The finite-dimensional probability measures are invariant under every
nonnegative integer-time translation, after coordinate reindexing. -/
theorem linearMarkovIntegerFiniteMarginalMeasure_map_natShiftReindex
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) (d : ℕ) :
    (linearMarkovIntegerFiniteMarginalMeasure initial transition
        (linearMarkovIntegerFiniteSetNatShift J d)).map
      (linearMarkovIntegerFiniteSetNatShiftReindex J d) =
    linearMarkovIntegerFiniteMarginalMeasure initial transition J := by
  let K := linearMarkovIntegerFiniteSetNatShift J d
  let reindex : (∀ _s : K, Ω) → (∀ _t : J, Ω) :=
    linearMarkovIntegerFiniteSetNatShiftReindex J d
  have hreindex : Measurable reindex :=
    linearMarkovIntegerFiniteSetNatShiftReindex_measurable J d
  change
    (linearMarkovIntegerFiniteMarginalPMF initial transition K).toMeasure.map
        reindex =
      (linearMarkovIntegerFiniteMarginalPMF initial transition J).toMeasure
  calc
    (linearMarkovIntegerFiniteMarginalPMF initial transition K).toMeasure.map
        reindex =
      ((linearMarkovIntegerFiniteMarginalPMF initial transition K).map
        reindex).toMeasure :=
      PMF.toMeasure_map
        (p := linearMarkovIntegerFiniteMarginalPMF initial transition K)
        (f := reindex) hreindex
    _ = (linearMarkovIntegerFiniteMarginalPMF initial transition J).toMeasure := by
      rw [show reindex = linearMarkovIntegerFiniteSetNatShiftReindex J d by rfl]
      exact congrArg PMF.toMeasure
        (linearMarkovIntegerFiniteMarginalPMF_map_natShiftReindex
          initial transition hdb J d)

/-- Mapping the full two-sided path law by a nonnegative integer-time shift
produces another projective limit of the same finite marginal family. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_natShift_isProjectiveLimit
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (d : ℕ) :
    IsProjectiveLimit (α := fun _ : ℤ => Ω)
      ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerPathShift ((d : ℕ) : ℤ)))
      (linearMarkovIntegerFiniteMarginalMeasure initial transition) := by
  intro J
  let K := linearMarkovIntegerFiniteSetNatShift J d
  let reindex : (∀ _s : K, Ω) → (∀ _t : J, Ω) :=
    linearMarkovIntegerFiniteSetNatShiftReindex J d
  have hshift : Measurable
      (linearMarkovIntegerPathShift ((d : ℕ) : ℤ) :
        (ℤ → Ω) → (ℤ → Ω)) :=
    linearMarkovIntegerPathShift_measurable _
  have hJ : Measurable
      (J.restrict : (ℤ → Ω) → (∀ _t : J, Ω)) :=
    J.measurable_restrict
  have hK : Measurable
      (K.restrict : (ℤ → Ω) → (∀ _s : K, Ω)) :=
    K.measurable_restrict
  have hreindex : Measurable reindex :=
    linearMarkovIntegerFiniteSetNatShiftReindex_measurable J d
  have hprojective :=
    linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
      initial transition hdb
  calc
    ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerPathShift ((d : ℕ) : ℤ))).map J.restrict =
      (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (J.restrict ∘ linearMarkovIntegerPathShift ((d : ℕ) : ℤ)) :=
      Measure.map_map hJ hshift
    _ = (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (reindex ∘ K.restrict) := by
      rw [linearMarkovIntegerFiniteSetRestrict_natShift]
    _ = ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        K.restrict).map reindex := by
      symm
      exact Measure.map_map hreindex hK
    _ = (linearMarkovIntegerFiniteMarginalMeasure initial transition K).map
        reindex := by
      rw [hprojective K]
    _ = linearMarkovIntegerFiniteMarginalMeasure initial transition J := by
      change
        (linearMarkovIntegerFiniteMarginalMeasure initial transition
          (linearMarkovIntegerFiniteSetNatShift J d)).map
            (linearMarkovIntegerFiniteSetNatShiftReindex J d) =
          linearMarkovIntegerFiniteMarginalMeasure initial transition J
      exact linearMarkovIntegerFiniteMarginalMeasure_map_natShiftReindex
        initial transition hdb J d

/-- The countably additive two-sided integer-time path law is invariant under
all nonnegative integer-time translations. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_natShift
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (d : ℕ) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerPathShift ((d : ℕ) : ℤ)) =
      linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  exact
    (linearMarkovTwoSidedIntegerPathMeasure_map_natShift_isProjectiveLimit
      initial transition hdb d).unique
      (linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
        initial transition hdb)

end

end MathlibAnalytic
end MGAP4D
