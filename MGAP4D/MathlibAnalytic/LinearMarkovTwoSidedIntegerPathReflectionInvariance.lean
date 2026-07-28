import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathReversal
import MGAP4D.MathlibAnalytic.LinearMarkovIntegerFiniteMarginalShift
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Global time reflection on a two-sided integer-time path. -/
def linearMarkovIntegerPathReflection
    (path : ℤ → Ω) : ℤ → Ω :=
  fun t => path (-t)

@[simp] theorem linearMarkovIntegerPathReflection_apply
    (path : ℤ → Ω) (t : ℤ) :
    linearMarkovIntegerPathReflection path t = path (-t) :=
  rfl

/-- Global integer-time reflection is involutive. -/
@[simp] theorem linearMarkovIntegerPathReflection_involutive :
    Function.Involutive (@linearMarkovIntegerPathReflection Ω) := by
  intro path
  funext t
  simp [linearMarkovIntegerPathReflection]

/-- Global integer-time reflection is measurable on the product path space. -/
theorem linearMarkovIntegerPathReflection_measurable :
    Measurable (@linearMarkovIntegerPathReflection Ω) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply (-t))

/-- Reflect every time in a finite set through the origin. -/
def linearMarkovIntegerFiniteSetReflection
    (J : Finset ℤ) : Finset ℤ :=
  J.image fun t => -t

@[simp] theorem linearMarkovIntegerFiniteSet_mem_reflection
    (J : Finset ℤ) (t : J) :
    -t.1 ∈ linearMarkovIntegerFiniteSetReflection J := by
  exact Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩

/-- Reindex values on the reflected finite time set back to the original set. -/
def linearMarkovIntegerFiniteSetReflectionReindex
    (J : Finset ℤ) :
    (∀ _s : linearMarkovIntegerFiniteSetReflection J, Ω) →
      (∀ _t : J, Ω) :=
  fun values t =>
    values ⟨-t.1, linearMarkovIntegerFiniteSet_mem_reflection J t⟩

/-- Reindexing a reflected finite product is measurable. -/
theorem linearMarkovIntegerFiniteSetReflectionReindex_measurable
    (J : Finset ℤ) :
    Measurable
      (linearMarkovIntegerFiniteSetReflectionReindex J :
        (∀ _s : linearMarkovIntegerFiniteSetReflection J, Ω) →
          (∀ _t : J, Ω)) := by
  exact measurable_pi_lambda _ (fun t =>
    measurable_pi_apply
      (⟨-t.1, linearMarkovIntegerFiniteSet_mem_reflection J t⟩ :
        linearMarkovIntegerFiniteSetReflection J))

/-- In a centered finite interval, the coordinate representing `-t` is the
reversal of the coordinate representing `t`. -/
theorem linearMarkovIntegerCenteredIndexOfBound_neg
    (r : ℕ) (t : ℤ)
    (ht : t.natAbs ≤ r)
    (hneg : (-t).natAbs ≤ r) :
    linearMarkovIntegerCenteredIndexOfBound r (-t) hneg =
      (linearMarkovIntegerCenteredIndexOfBound r t ht).rev := by
  apply linearMarkovIntegerCenteredTime_injective r
  rw [linearMarkovIntegerCenteredTime_indexOfBound]
  rw [linearMarkovIntegerCenteredTime_rev]
  rw [linearMarkovIntegerCenteredTime_indexOfBound]

/-- Observe the reflected finite time set and reindex its values back to the
original time set. -/
def linearMarkovIntegerFiniteSetReflectionObserveAt
    (J : Finset ℤ) (r : ℕ)
    (hReflection : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetReflection J) ≤ r) :
    LinearMarkovIntegerCenteredFinitePath Ω r → (∀ _t : J, Ω) :=
  fun path =>
    linearMarkovIntegerFiniteSetReflectionReindex J
      (linearMarkovIntegerFiniteSetObserveAt
        (linearMarkovIntegerFiniteSetReflection J) r hReflection path)

/-- Reflecting the finite path before observing `J` is exactly observing the
reflected time set and reindexing back to `J`. -/
theorem linearMarkovIntegerFiniteSetReflectionObserveAt_eq_comp_reverse
    (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r)
    (hReflection : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetReflection J) ≤ r) :
    (linearMarkovIntegerFiniteSetReflectionObserveAt J r hReflection :
      LinearMarkovIntegerCenteredFinitePath Ω r → (∀ _t : J, Ω)) =
      linearMarkovIntegerFiniteSetObserveAt J r hJ ∘
        linearMarkovFinitePathReverse := by
  funext path t
  unfold linearMarkovIntegerFiniteSetReflectionObserveAt
    linearMarkovIntegerFiniteSetReflectionReindex
    linearMarkovIntegerFiniteSetObserveAt
    linearMarkovIntegerFiniteSetIndexAt
    linearMarkovFinitePathReverse
  apply congrArg path
  have ht : t.1.natAbs ≤ r :=
    (linearMarkovIntegerFiniteSet_natAbs_le_radius J t.2).trans hJ
  have hneg : (-t.1).natAbs ≤ r :=
    (linearMarkovIntegerFiniteSet_natAbs_le_radius
      (linearMarkovIntegerFiniteSetReflection J)
      (linearMarkovIntegerFiniteSet_mem_reflection J t)).trans hReflection
  simpa using linearMarkovIntegerCenteredIndexOfBound_neg r t.1 ht hneg

/-- Every common-radius finite observation of a detailed-balanced Markov path is
invariant under global time reflection. -/
theorem linearMarkovIntegerCenteredFinitePathPMF_map_reflectionObserveAt
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) (r : ℕ)
    (hJ : linearMarkovIntegerFiniteSetRadius J ≤ r)
    (hReflection : linearMarkovIntegerFiniteSetRadius
      (linearMarkovIntegerFiniteSetReflection J) ≤ r) :
    (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetReflectionObserveAt J r hReflection) =
      (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetObserveAt J r hJ) := by
  have hbase :
      linearMarkovIntegerCenteredFinitePathPMF initial transition r =
        linearMarkovFinitePathPMF initial transition (2 * r + 2) := by
    exact linearMarkovChronologicalCenteredFinitePathPMF_eq_finitePathPMF
      initial transition r
  rw [hbase]
  rw [linearMarkovIntegerFiniteSetReflectionObserveAt_eq_comp_reverse
    (Ω := Ω) J r hJ hReflection]
  rw [← PMF.map_comp]
  rw [linearMarkovFinitePathPMF_map_reverse_of_detailedBalance
    initial transition hdb (2 * r + 2)]

/-- Every arbitrary finite integer-time marginal is invariant under reflection,
after canonical coordinate reindexing. -/
theorem linearMarkovIntegerFiniteMarginalPMF_map_reflectionReindex
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) :
    (linearMarkovIntegerFiniteMarginalPMF initial transition
        (linearMarkovIntegerFiniteSetReflection J)).map
      (linearMarkovIntegerFiniteSetReflectionReindex J) =
    linearMarkovIntegerFiniteMarginalPMF initial transition J := by
  let K := linearMarkovIntegerFiniteSetReflection J
  let r := max (linearMarkovIntegerFiniteSetRadius J)
    (linearMarkovIntegerFiniteSetRadius K)
  have hJ : linearMarkovIntegerFiniteSetRadius J ≤ r :=
    le_max_left _ _
  have hK : linearMarkovIntegerFiniteSetRadius K ≤ r :=
    le_max_right _ _
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    initial transition hdb K r hK]
  rw [PMF.map_comp]
  change
    (linearMarkovIntegerCenteredFinitePathPMF initial transition r).map
        (linearMarkovIntegerFiniteSetReflectionObserveAt J r hK) =
      linearMarkovIntegerFiniteMarginalPMF initial transition J
  rw [← linearMarkovIntegerCenteredFinitePathPMF_map_observeAt
    initial transition hdb J r hJ]
  exact linearMarkovIntegerCenteredFinitePathPMF_map_reflectionObserveAt
    initial transition hdb J r hJ hK

/-- Reflection invariance of arbitrary finite-dimensional probability measures. -/
theorem linearMarkovIntegerFiniteMarginalMeasure_map_reflectionReindex
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (J : Finset ℤ) :
    (linearMarkovIntegerFiniteMarginalMeasure initial transition
        (linearMarkovIntegerFiniteSetReflection J)).map
      (linearMarkovIntegerFiniteSetReflectionReindex J) =
    linearMarkovIntegerFiniteMarginalMeasure initial transition J := by
  let K := linearMarkovIntegerFiniteSetReflection J
  let reindex : (∀ _s : K, Ω) → (∀ _t : J, Ω) :=
    linearMarkovIntegerFiniteSetReflectionReindex J
  have hreindex : Measurable reindex :=
    linearMarkovIntegerFiniteSetReflectionReindex_measurable J
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
      change
        ((linearMarkovIntegerFiniteMarginalPMF initial transition
          (linearMarkovIntegerFiniteSetReflection J)).map
            (linearMarkovIntegerFiniteSetReflectionReindex J)).toMeasure =
          (linearMarkovIntegerFiniteMarginalPMF initial transition J).toMeasure
      exact congrArg PMF.toMeasure
        (linearMarkovIntegerFiniteMarginalPMF_map_reflectionReindex
          initial transition hdb J)

/-- Restricting a globally reflected full path to `J` equals restricting the
original path to the reflected set and reindexing back to `J`. -/
theorem linearMarkovIntegerFiniteSetRestrict_reflection
    (J : Finset ℤ) :
    (J.restrict ∘ (@linearMarkovIntegerPathReflection Ω)) =
      linearMarkovIntegerFiniteSetReflectionReindex J ∘
        (linearMarkovIntegerFiniteSetReflection J).restrict := by
  funext path t
  rfl

/-- Mapping the full path law by global time reflection produces another
projective limit of the same finite marginal family. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_reflection_isProjectiveLimit
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    IsProjectiveLimit (α := fun _ : ℤ => Ω)
      ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        linearMarkovIntegerPathReflection)
      (linearMarkovIntegerFiniteMarginalMeasure initial transition) := by
  intro J
  let K := linearMarkovIntegerFiniteSetReflection J
  let reindex : (∀ _s : K, Ω) → (∀ _t : J, Ω) :=
    linearMarkovIntegerFiniteSetReflectionReindex J
  have hreflection : Measurable (@linearMarkovIntegerPathReflection Ω) :=
    linearMarkovIntegerPathReflection_measurable
  have hJ : Measurable
      (J.restrict : (ℤ → Ω) → (∀ _t : J, Ω)) :=
    J.measurable_restrict
  have hK : Measurable
      (K.restrict : (ℤ → Ω) → (∀ _s : K, Ω)) :=
    K.measurable_restrict
  have hreindex : Measurable reindex :=
    linearMarkovIntegerFiniteSetReflectionReindex_measurable J
  have hprojective :=
    linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
      initial transition hdb
  calc
    ((linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        linearMarkovIntegerPathReflection).map J.restrict =
      (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (J.restrict ∘ linearMarkovIntegerPathReflection) :=
      Measure.map_map hJ hreflection
    _ = (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        (reindex ∘ K.restrict) := by
      rw [linearMarkovIntegerFiniteSetRestrict_reflection]
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
          (linearMarkovIntegerFiniteSetReflection J)).map
            (linearMarkovIntegerFiniteSetReflectionReindex J) =
          linearMarkovIntegerFiniteMarginalMeasure initial transition J
      exact linearMarkovIntegerFiniteMarginalMeasure_map_reflectionReindex
        initial transition hdb J

/-- The countably additive two-sided integer-time path law is invariant under
global time reflection `t ↦ -t`. -/
theorem linearMarkovTwoSidedIntegerPathMeasure_map_reflection
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition) :
    (linearMarkovTwoSidedIntegerPathMeasure initial transition hdb).map
        linearMarkovIntegerPathReflection =
      linearMarkovTwoSidedIntegerPathMeasure initial transition hdb := by
  exact
    (linearMarkovTwoSidedIntegerPathMeasure_map_reflection_isProjectiveLimit
      initial transition hdb).unique
      (linearMarkovTwoSidedIntegerPathMeasure_isProjectiveLimit
        initial transition hdb)

end

end MathlibAnalytic
end MGAP4D
