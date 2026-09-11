import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSNull
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathShiftInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Restriction of a two-sided integer path to its nonnegative half is measurable. -/
theorem measurable_linearMarkovIntegerPathNonnegativeRestriction :
    Measurable (@linearMarkovIntegerPathNonnegativeRestriction Ω) := by
  exact measurable_pi_lambda _ (fun t => measurable_pi_apply ((t : ℕ) : ℤ))

/-- Restricting a one-step translated full path to nonnegative times is the
one-step natural-time shift of the original restriction. -/
@[simp] theorem linearMarkovIntegerPathNonnegativeRestriction_shift_one
    (path : ℤ → Ω) :
    linearMarkovIntegerPathNonnegativeRestriction
        (linearMarkovIntegerPathShift (1 : ℤ) path) =
      linearMarkovPathShift
        (linearMarkovIntegerPathNonnegativeRestriction path) := by
  funext t
  unfold linearMarkovIntegerPathNonnegativeRestriction
    linearMarkovIntegerPathShift linearMarkovPathShift
  apply congrArg path
  omega

/-- Reflecting after translating by one and then shifting the positive half once
cancels the translation. -/
@[simp] theorem linearMarkovPathShift_nonnegativeRestriction_reflection_shift_one
    (path : ℤ → Ω) :
    linearMarkovPathShift
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection
            (linearMarkovIntegerPathShift (1 : ℤ) path))) =
      linearMarkovIntegerPathNonnegativeRestriction
        (linearMarkovIntegerPathReflection path) := by
  funext t
  unfold linearMarkovPathShift
    linearMarkovIntegerPathNonnegativeRestriction
    linearMarkovIntegerPathReflection linearMarkovIntegerPathShift
  apply congrArg path
  omega

/-- One positive-time translation can be moved between the two slots of the full
path-space temporal Osterwalder--Schrader form. -/
theorem linearMarkovTwoSidedIntegerPathOSForm_shift_left_eq_shift_right
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        (linearMarkovPositiveTimeShiftAlgHom F) G =
      linearMarkovTwoSidedIntegerPathOSForm initial transition hdb
        F (linearMarkovPositiveTimeShiftAlgHom G) := by
  let μ := linearMarkovTwoSidedIntegerPathMeasure initial transition hdb
  let L : (ℤ → Ω) → ℝ := fun path =>
    (((linearMarkovPositiveTimeShiftAlgHom F :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)
      (linearMarkovIntegerPathNonnegativeRestriction
        (linearMarkovIntegerPathReflection path))) *
    ((G : (ℕ → Ω) → ℝ)
      (linearMarkovIntegerPathNonnegativeRestriction path))
  have hN : Measurable
      (@linearMarkovIntegerPathNonnegativeRestriction Ω) :=
    measurable_linearMarkovIntegerPathNonnegativeRestriction
  have hR : Measurable (@linearMarkovIntegerPathReflection Ω) :=
    linearMarkovIntegerPathReflection_measurable
  have hShiftF : Measurable
      (((linearMarkovPositiveTimeShiftAlgHom F :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)) :=
    measurable_linearMarkovPositiveTimeCylinder
      (linearMarkovPositiveTimeShiftAlgHom F)
  have hG : Measurable ((G : (ℕ → Ω) → ℝ)) :=
    measurable_linearMarkovPositiveTimeCylinder G
  have hL : StronglyMeasurable L := by
    exact ((hShiftF.comp (hN.comp hR)).mul (hG.comp hN)).stronglyMeasurable
  change (∫ path, L path ∂μ) =
    ∫ path,
      ((F : (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction
          (linearMarkovIntegerPathReflection path))) *
      (((linearMarkovPositiveTimeShiftAlgHom G :
        linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
          (ℕ → Ω) → ℝ)
        (linearMarkovIntegerPathNonnegativeRestriction path)) ∂μ
  calc
    (∫ path, L path ∂μ) =
        ∫ path, L path
          ∂μ.map (linearMarkovIntegerPathShift (1 : ℤ)) := by
      rw [linearMarkovTwoSidedIntegerPathMeasure_map_shift
        initial transition hdb (1 : ℤ)]
    _ = ∫ path, L (linearMarkovIntegerPathShift (1 : ℤ) path) ∂μ := by
      exact MeasureTheory.integral_map_of_stronglyMeasurable
        (linearMarkovIntegerPathShift_measurable (1 : ℤ)) hL
    _ = ∫ path,
        ((F : (ℕ → Ω) → ℝ)
          (linearMarkovIntegerPathNonnegativeRestriction
            (linearMarkovIntegerPathReflection path))) *
        (((linearMarkovPositiveTimeShiftAlgHom G :
          linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
            (ℕ → Ω) → ℝ)
          (linearMarkovIntegerPathNonnegativeRestriction path)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path => by
        unfold L
        change
          (F : (ℕ → Ω) → ℝ)
              (linearMarkovPathShift
                (linearMarkovIntegerPathNonnegativeRestriction
                  (linearMarkovIntegerPathReflection
                    (linearMarkovIntegerPathShift (1 : ℤ) path)))) *
            (G : (ℕ → Ω) → ℝ)
              (linearMarkovIntegerPathNonnegativeRestriction
                (linearMarkovIntegerPathShift (1 : ℤ) path)) =
          (F : (ℕ → Ω) → ℝ)
              (linearMarkovIntegerPathNonnegativeRestriction
                (linearMarkovIntegerPathReflection path)) *
            (G : (ℕ → Ω) → ℝ)
              (linearMarkovPathShift
                (linearMarkovIntegerPathNonnegativeRestriction path))
        rw [linearMarkovPathShift_nonnegativeRestriction_reflection_shift_one]
        rw [linearMarkovIntegerPathNonnegativeRestriction_shift_one]

/-- The one-step positive-time shift preserves the full path-space OS null
submodule. -/
theorem linearMarkovPositiveTimeShift_mem_twoSidedIntegerPathOSNull
    (initial : PMF Ω) (transition : Ω → PMF Ω)
    (hdb : LinearMarkovDetailedBalanceReal initial transition)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω))
    (hF : F ∈ linearMarkovTwoSidedIntegerPathOSNull initial transition hdb) :
    linearMarkovPositiveTimeShiftAlgHom F ∈
      linearMarkovTwoSidedIntegerPathOSNull initial transition hdb := by
  rw [mem_linearMarkovTwoSidedIntegerPathOSNull_iff_forall_orthogonal] at hF ⊢
  intro G
  rw [linearMarkovTwoSidedIntegerPathOSForm_shift_left_eq_shift_right]
  exact hF (linearMarkovPositiveTimeShiftAlgHom G)

end

end MathlibAnalytic
end MGAP4D
