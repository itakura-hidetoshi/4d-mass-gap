import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactGapInterval
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Exact-threshold separation for the complete Yang--Mills direct bounded
construction route.

The exact gap interval theorem identifies `exactGapValueReal` as the least
nonzero spectral value.  This file turns that order statement into exact
sublevel-set classifications: below the threshold only the vacuum remains, and
at or below the threshold the spectrum consists exactly of the vacuum and the
attained exact gap.

All results remain parametrized by the existing complete construction spine.
They do not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- The nonzero spectrum is disjoint from the open ray below the exact gap. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_disjoint_Iio_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Disjoint
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      (Set.Iio exactGapValueReal) := by
  rw [Set.disjoint_left]
  intro E hE hBelow
  have hLower : exactGapValueReal ≤ E :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_exactGapRay S hE
  exact (not_lt_of_ge hLower hBelow).elim

/-- Strictly below the exact gap, the complete energy spectrum contains only the
vacuum point. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iio_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩ Set.Iio exactGapValueReal =
      ({0} : Set ℝ) := by
  ext E
  constructor
  · intro hE
    rcases hE with ⟨hSpectrum, hBelow⟩
    have hUnion :=
      euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_subset_vacuum_union_exactGapRay S
        hSpectrum
    rcases hUnion with hVacuum | hRay
    · simpa using hVacuum
    · exact (not_lt_of_ge hRay hBelow).elim
  · intro hVacuum
    have hE0 : E = 0 := by
      simpa using hVacuum
    subst E
    exact ⟨
      S.definitionBridge.spine.model.vacuumEnergyZero,
      (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S).1⟩

/-- The nonzero spectrum at or below the exact threshold is the singleton exact
spectral-gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_inter_Iic_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) ∩
        Set.Iic exactGapValueReal =
      ({exactGapValueReal} : Set ℝ) := by
  ext E
  constructor
  · intro hE
    rcases hE with ⟨hNonzeroSpectrum, hUpper⟩
    have hLower : exactGapValueReal ≤ E :=
      (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S).2
        hNonzeroSpectrum
    have hEq : E = exactGapValueReal := le_antisymm hUpper hLower
    simpa [hEq]
  · intro hSingleton
    have hEq : E = exactGapValueReal := by
      simpa using hSingleton
    subst E
    exact ⟨
      (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S).1,
      le_rfl⟩

/-- The full spectrum at or below the exact threshold consists exactly of the
vacuum and the attained exact-gap point. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_inter_Iic_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ∩ Set.Iic exactGapValueReal =
      ({0, exactGapValueReal} : Set ℝ) := by
  ext E
  constructor
  · intro hE
    rcases hE with ⟨hSpectrum, hUpper⟩
    by_cases hE0 : E = 0
    · simp [hE0]
    · have hNonzeroSpectrum :
          E ∈ S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) := by
        exact ⟨hSpectrum, by simpa using hE0⟩
      have hLower : exactGapValueReal ≤ E :=
        (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S).2
          hNonzeroSpectrum
      have hEq : E = exactGapValueReal := le_antisymm hUpper hLower
      simp [hEq]
  · intro hPair
    have hCases : E = 0 ∨ E = exactGapValueReal := by
      simpa using hPair
    rcases hCases with hE0 | hEGap
    · subst E
      exact ⟨
        S.definitionBridge.spine.model.vacuumEnergyZero,
        le_of_lt
          (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S).1⟩
    · subst E
      exact ⟨
        euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum S,
        le_rfl⟩

end

end MathlibAnalytic
end MGAP4D
