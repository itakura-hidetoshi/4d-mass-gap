import MGAP4D.MathlibAnalytic.KolmogorovPolishExtension
import Mathlib.MeasureTheory.Measure.Tight

namespace MGAP4D
namespace MathlibAnalytic

open Set MeasureTheory
open scoped ENNReal

noncomputable section

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)]
  {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

/-- Exact compact-tightness input needed to extend a projective cylinder
content.  The condition is finite-dimensional compact inner regularity; in
particular every finite marginal is a tight measure. -/
structure ProjectiveFamilyCompactTightnessData
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) where
  innerRegular :
    ∀ J,
      (P J).InnerRegularWRT
        (fun s => IsCompact s ∧ IsClosed s) MeasurableSet

/-- Every finite marginal covered by the compact-tightness data is tight. -/
theorem ProjectiveFamilyCompactTightnessData.finiteMarginalTight
    [∀ J, IsFiniteMeasure (P J)]
    (T : ProjectiveFamilyCompactTightnessData P)
    (J : Finset ι) :
    IsTightMeasureSet {P J} :=
  isTightMeasureSet_singleton_of_innerRegularWRT (T.innerRegular J)

/-- Extend a projective family from its cylinder content using compact
inner-regularity rather than a global Polish-space assumption. -/
noncomputable def compactTightKolmogorovProjectiveLimit
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j))
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P)
    (T : ProjectiveFamilyCompactTightnessData P) :
    Measure (∀ i, α i) :=
  (projectiveFamilyContent hP).measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm.le
    (projectiveFamilyContent_sigmaSubadditive_of_innerRegular
      hP T.innerRegular)

/-- The compact-tightness construction realizes every prescribed finite
marginal. -/
theorem isProjectiveLimit_compactTightKolmogorovProjectiveLimit
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P)
    (T : ProjectiveFamilyCompactTightnessData P) :
    IsProjectiveLimit
      (compactTightKolmogorovProjectiveLimit P hP T) P := by
  intro J
  ext s hs
  rw [Measure.map_apply]
  · have hmem : J.restrict ⁻¹' s ∈ measurableCylinders α :=
      (mem_measurableCylinders _).mpr ⟨J, s, hs, rfl⟩
    rw [compactTightKolmogorovProjectiveLimit,
      AddContent.measure_eq _ _ _ _ hmem]
    · simpa only [cylinder] using
        (projectiveFamilyContent_cylinder hP hs)
    · exact generateFrom_measurableCylinders.symm
  · exact J.measurable_restrict
  · exact hs

/-- Existence form of the compact-tightness extension route. -/
theorem compactTight_kolmogorov_projective_limit_exists
    [∀ J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P)
    (T : ProjectiveFamilyCompactTightnessData P) :
    ∃ μ : Measure (∀ i, α i), IsProjectiveLimit μ P :=
  ⟨compactTightKolmogorovProjectiveLimit P hP T,
    isProjectiveLimit_compactTightKolmogorovProjectiveLimit hP T⟩

/-- Probability normalization passes to the compact-tightness extension. -/
theorem compactTightKolmogorovProjectiveLimit_probability
    [Nonempty ι]
    [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P)
    (T : ProjectiveFamilyCompactTightnessData P) :
    IsProbabilityMeasure
      (compactTightKolmogorovProjectiveLimit P hP T) :=
  MeasureTheory.IsProjectiveLimit.isProbabilityMeasure
    (isProjectiveLimit_compactTightKolmogorovProjectiveLimit hP T)

end

end MathlibAnalytic
end MGAP4D
