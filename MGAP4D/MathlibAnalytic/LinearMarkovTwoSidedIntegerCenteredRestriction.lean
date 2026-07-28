import MGAP4D.MathlibAnalytic.LinearMarkovChronologicalCenteredPathFinitePathPMF
import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalShift
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathReflectionInvariance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The finite set of all integer times represented by the centered chronological
window `[-n-1, n+1]`. -/
def linearMarkovIntegerCenteredTimeSet (n : ℕ) : Finset ℤ :=
  Finset.univ.image (@linearMarkovIntegerCenteredTime n)

@[simp] theorem linearMarkovIntegerCenteredTime_mem_timeSet
    (n : ℕ) (i : Fin (2 * n + 3)) :
    linearMarkovIntegerCenteredTime i ∈
      linearMarkovIntegerCenteredTimeSet n := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Reindex values on the finite centered time set into chronological order. -/
def linearMarkovIntegerCenteredTimeSetReindex
    (n : ℕ) :
    (∀ _t : linearMarkovIntegerCenteredTimeSet n, Ω) →
      LinearMarkovIntegerCenteredFinitePath Ω n :=
  fun values i =>
    values ⟨linearMarkovIntegerCenteredTime i,
      linearMarkovIntegerCenteredTime_mem_timeSet n i⟩

/-- Restrict a full two-sided path to the centered chronological window. -/
def linearMarkovIntegerCenteredPathRestriction
    (n : ℕ) (path : ℤ → Ω) :
    LinearMarkovIntegerCenteredFinitePath Ω n :=
  fun i => path (linearMarkovIntegerCenteredTime i)

/-- Centered restriction factors through ordinary finite-set restriction. -/
theorem linearMarkovIntegerCenteredPathRestriction_eq_reindex_comp_restrict
    (n : ℕ) :
    (@linearMarkovIntegerCenteredPathRestriction Ω n) =
      linearMarkovIntegerCenteredTimeSetReindex n ∘
        (linearMarkovIntegerCenteredTimeSet n).restrict := by
  rfl

/-- Reindexing the finite centered time set is measurable. -/
theorem linearMarkovIntegerCenteredTimeSetReindex_measurable
    (n : ℕ) :
    Measurable (@linearMarkovIntegerCenteredTimeSetReindex Ω _ _ _ n) := by
  exact measurable_pi_lambda _ (fun i =>
    measurable_pi_apply
      (⟨linearMarkovIntegerCenteredTime i,
        linearMarkovIntegerCenteredTime_mem_timeSet n i⟩ :
          linearMarkovIntegerCenteredTimeSet n))

/-- Restriction to a centered chronological window is measurable. -/
theorem linearMarkovIntegerCenteredPathRestriction_measurable
    (n : ℕ) :
    Measurable (@linearMarkovIntegerCenteredPathRestriction Ω _ _ _ n) := by
  exact measurable_pi_lambda _ (fun i =>
    measurable_pi_apply (linearMarkovIntegerCenteredTime i))

/-- The canonical radius of the complete centered time set is bounded by its
outer endpoint `n+1`. -/
theorem linearMarkovIntegerCenteredTimeSet_radius_le
    (n : ℕ) :
    linearMarkovIntegerFiniteSetRadius
        (linearMarkovIntegerCenteredTimeSet n) ≤ n + 1 := by
  unfold linearMarkovIntegerFiniteSetRadius
  apply Finset.sup_le
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨i, _hi, rfl⟩
  rw [Int.natAbs_le]
  exact ⟨linearMarkovIntegerCenteredTime_lower i,
    linearMarkovIntegerCenteredTime_upper i⟩

/-- Observing every centered time in the next larger projective window and
reindexing gives exactly the one-step central restriction. -/
theorem linearMarkovIntegerCenteredTimeSetReindex_observeAt
    (n : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerCenteredTimeSet n) ≤ n + 1) :
    linearMarkovIntegerCenteredTimeSetReindex n ∘
        linearMarkovIntegerFiniteSetObserveAt
          (linearMarkovIntegerCenteredTimeSet n) (n + 1) hJ =
      linearMarkovIntegerCenteredFinitePathRestrictBy n 1 := by
  funext path i
  unfold linearMarkovIntegerCenteredTimeSetReindex
    linearMarkovIntegerFiniteSetObserveAt
    linearMarkovIntegerFiniteSetIndexAt
  rw [linearMarkovIntegerCenteredFinitePathRestrictBy_apply]
  apply congrArg path
  apply linearMarkovIntegerCenteredTime_injective (n + 1)
  rw [linearMarkovIntegerCenteredTime_indexOfBound]
  rw [linearMarkovIntegerCenteredTime_indexEmbed]

/-- The arbitrary finite marginal on the complete centered time set, reindexed
chronologically, is the existing centered finite Markov path PMF. -/
theorem linearMarkovIntegerFiniteMarginalPMF_map_centeredTimeSetReindex
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovIntegerFiniteMarginalPMF initial transition
        (linearMarkovIntegerCenteredTimeSet n)).map
      (linearMarkovIntegerCenteredTimeSetReindex n) =
        linearMarkovIntegerCenteredFinitePathPMF initial transition n := by
  let hJ := linearMarkovIntegerCenteredTimeSet_radius_le n
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    initial transition hdb (linearMarkovIntegerCenteredTimeSet n) (n + 1) hJ]
  rw [PMF.map_comp]
  rw [linearMarkovIntegerCenteredTimeSetReindex_observeAt n hJ]
  exact linearMarkovIntegerCenteredFinitePathPMF_map_restrictBy_of_detailedBalance
    initial transition hdb n 1

/-- Measure form of the centered finite-window marginal identity. -/
theorem linearMarkovIntegerFiniteMarginalMeasure_map_centeredTimeSetReindex
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovIntegerFiniteMarginalMeasure initial transition
        (linearMarkovIntegerCenteredTimeSet n)).map
      (linearMarkovIntegerCenteredTimeSetReindex n) =
        (linearMarkovIntegerCenteredFinitePathPMF initial transition n).toMeasure := by
  unfold linearMarkovIntegerFiniteMarginalMeasure
  rw [PMF.toMeasure_map
    (p := linearMarkovIntegerFiniteMarginalPMF initial transition
      (linearMarkovIntegerCenteredTimeSet n))
    (f := linearMarkovIntegerCenteredTimeSetReindex n)
    (linearMarkovIntegerCenteredTimeSetReindex_measurable n)]
  exact congrArg PMF.toMeasure
    (linearMarkovIntegerFiniteMarginalPMF_map_centeredTimeSetReindex
      initial transition hdb n)

/-- Every centered chronological restriction of the full two-sided path measure
has exactly the corresponding finite Markov path law. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_centeredRestriction
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerCenteredPathRestriction n) =
      (linearMarkovIntegerCenteredFinitePathPMF initial transition n).toMeasure := by
  let J := linearMarkovIntegerCenteredTimeSet n
  let reindex : (∀ _t : J, Ω) →
      LinearMarkovIntegerCenteredFinitePath Ω n :=
    linearMarkovIntegerCenteredTimeSetReindex n
  have hJ : Measurable (J.restrict : (ℤ → Ω) → (∀ _t : J, Ω)) :=
    J.measurable_restrict
  have hreindex : Measurable reindex :=
    linearMarkovIntegerCenteredTimeSetReindex_measurable n
  have hprojective :=
    linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
      initial transition hdb
  calc
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (linearMarkovIntegerCenteredPathRestriction n) =
      (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (reindex ∘ J.restrict) := by
          rw [linearMarkovIntegerCenteredPathRestriction_eq_reindex_comp_restrict]
    _ = ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
          J.restrict).map reindex := by
          symm
          exact Measure.map_map hreindex hJ
    _ = (linearMarkovIntegerFiniteMarginalMeasure initial transition J).map
          reindex := by
          rw [hprojective J]
    _ = (linearMarkovIntegerCenteredFinitePathPMF initial transition n).toMeasure := by
          exact linearMarkovIntegerFiniteMarginalMeasure_map_centeredTimeSetReindex
            initial transition hdb n

/-- Integration of a finite centered-window observable under the full path law is
exactly its finite-PMF expectation. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_integral_centeredRestriction
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (n : ℕ)
    (H : LinearMarkovIntegerCenteredFinitePath Ω n → ℝ) :
    (∫ path, H (linearMarkovIntegerCenteredPathRestriction n path)
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb) =
      finitePMFExpectationReal
        (linearMarkovIntegerCenteredFinitePathPMF initial transition n) H := by
  have hrestrict := linearMarkovIntegerCenteredPathRestriction_measurable
    (Ω := Ω) n
  have hH : StronglyMeasurable H := (measurable_of_finite H).stronglyMeasurable
  calc
    (∫ path, H (linearMarkovIntegerCenteredPathRestriction n path)
      ∂linearMarkovTwoSidedIntegerPathMeasure initial transition hdb) =
      ∫ centered, H centered
        ∂(linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
          (linearMarkovIntegerCenteredPathRestriction n) := by
            symm
            exact MeasureTheory.integral_map_of_stronglyMeasurable
              hrestrict hH
    _ = ∫ centered, H centered
        ∂(linearMarkovIntegerCenteredFinitePathPMF initial transition n).toMeasure := by
          rw [linearMarkovTwoSidedIntegerPathMeasure_map_centeredRestriction
            initial transition hdb n]
    _ = finitePMFExpectationReal
        (linearMarkovIntegerCenteredFinitePathPMF initial transition n) H := by
          rw [PMF.integral_eq_sum]
          simp [finitePMFExpectationReal]

end

end MathlibAnalytic
end MGAP4D
