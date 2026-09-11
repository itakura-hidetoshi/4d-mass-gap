import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Uniqueness of the mass-gap witness for the complete Yang--Mills direct bounded
construction route.

The model-level mass-gap predicate is existential.  The exact-gap and exact
first-excitation packages identify its spectral threshold with an attained least
nonzero spectral value.  This file proves that every mass-gap witness is forced
to be that value and identifies the model's displayed `massGapValue` with the
same canonical threshold.

All statements remain parametrized by the existing complete construction spine.
They do not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- Predicate carried by a model-level mass-gap witness. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (m : ℝ) : Prop :=
    0 < m ∧
      m ∈ S.definitionBridge.spine.model.energySpectrum ∧
      m = sInf
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))

/-- The model's displayed mass-gap value is the exact spectral threshold. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.massGapValue = exactGapValueReal := by
  calc
    S.definitionBridge.spine.model.massGapValue =
        S.definitionBridge.spine.model.firstExcitation :=
      S.definitionBridge.spine.model.massGapValue_eq_firstExcitation
    _ = exactGapValueReal :=
      euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S

/-- The exact gap is a model-level mass-gap witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGap_massGapWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp
      S exactGapValueReal := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S).1,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_eq_nonzeroSpectrum_sInf S⟩

/-- The model's displayed mass-gap value is a mass-gap witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_massGapWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp
      S S.definitionBridge.spine.model.massGapValue := by
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S] using
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_massGapWitness S

/-- Every model-level mass-gap witness equals the exact gap. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    {m : ℝ}
    (hm : euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m) :
    m = exactGapValueReal := by
  calc
    m = sInf
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) :=
      hm.2.2
    _ = exactGapValueReal :=
      euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_sInf_eq_exactGap S

/-- Every model-level mass-gap witness equals the model first excitation. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_firstExcitation
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    {m : ℝ}
    (hm : euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m) :
    m = S.definitionBridge.spine.model.firstExcitation := by
  calc
    m = exactGapValueReal :=
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_exactGap S hm
    _ = S.definitionBridge.spine.model.firstExcitation :=
      (euclideanYangMillsCompleteConstructionDirectBounded_firstExcitation_eq_exactGapValueReal S).symm

/-- Every model-level mass-gap witness equals the displayed mass-gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_massGapValue
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    {m : ℝ}
    (hm : euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m) :
    m = S.definitionBridge.spine.model.massGapValue := by
  calc
    m = exactGapValueReal :=
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_exactGap S hm
    _ = S.definitionBridge.spine.model.massGapValue :=
      (euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S).symm

/-- The complete construction has a unique model-level mass-gap witness. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃! m : ℝ,
      euclideanYangMillsCompleteConstructionDirectBounded_massGapWitnessProp S m := by
  refine ⟨
    exactGapValueReal,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_massGapWitness S,
    ?_⟩
  intro m hm
  exact
    euclideanYangMillsCompleteConstructionDirectBounded_massGapWitness_eq_exactGap S hm

/-- The displayed mass-gap value is the least nonzero spectral energy. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_isLeast_nonzeroSpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      S.definitionBridge.spine.model.massGapValue := by
  rw [
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S]
  exact
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S

/-- The exact-gap PVM witness is also supported at the displayed mass-gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_massGapValuePVMWitness
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    ∃ ψ : S.definitionBridge.spine.model.H,
      ψ ∈ S.definitionBridge.spine.model.spectralPVM
        ({S.definitionBridge.spine.model.massGapValue} : Set ℝ) := by
  rcases
      euclideanYangMillsCompleteConstructionDirectBounded_exactGapPVMWitness S with
    ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S] using
    hψ

/-- Strictly below the displayed mass-gap value, the spectrum is the vacuum only. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_massGapValue
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iio S.definitionBridge.spine.model.massGapValue =
      ({0} : Set ℝ) := by
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S] using
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_exactGap S

/-- At or below the displayed mass-gap value, the spectrum is exactly the vacuum
and mass-gap pair. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_massGapValue
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩
        Set.Iic S.definitionBridge.spine.model.massGapValue =
      ({0, S.definitionBridge.spine.model.massGapValue} : Set ℝ) := by
  simpa [
    euclideanYangMillsCompleteConstructionDirectBounded_massGapValue_eq_exactGapValueReal S] using
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_exactGap S

end

end MathlibAnalytic
end MGAP4D
