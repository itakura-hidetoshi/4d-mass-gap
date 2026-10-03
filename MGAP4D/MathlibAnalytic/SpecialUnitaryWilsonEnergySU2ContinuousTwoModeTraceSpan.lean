import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNHaarTwoModeSpan
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNTwoModeContinuousBoundaryRepresentative
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-!
# Continuous Wilson two-mode span equals the literal SU(2) trace span

The normalized-Haar Gram--Schmidt two-mode family already has the same L2 span
as the literal seed pair `1, E_W`.  The chosen continuous representatives map
exactly to those L2 modes, while `ContinuousMap.toLp` is injective for
normalized compact Haar because Haar has full support.

Hence the span equality lifts back from L2 to continuous class functions
without computing any Gram--Schmidt coefficient.

For SU(2), `E_W = 1 - r`, where `r` is the normalized real trace.  Therefore
the same continuous two-mode carrier is exactly `span {1,r}`.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance su2ContinuousTwoModeSpanTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance su2ContinuousTwoModeSpanCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance su2ContinuousTwoModeSpanSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance su2ContinuousTwoModeSpanMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance su2ContinuousTwoModeSpanBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance su2ContinuousTwoModeSpanHaarOpenPos (N : ℕ) :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- Each chosen continuous Gram--Schmidt mode belongs to the literal continuous
seed span. -/
theorem specialUnitaryWilsonContinuousTwoMode_mem_seed_span
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    specialUnitaryWilsonContinuousTwoMode hN2 k ∈
      Submodule.span ℝ
        (Set.range (specialUnitaryWilsonContinuousTwoModeSeed N)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hL2 :=
    specialUnitaryWilsonHaarTwoMode_mem_seed_span hN2 k
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hL2
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ?_
  refine ⟨a, ?_⟩
  apply
    (ContinuousMap.toLp_injective
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) μ)
  calc
    ContinuousMap.toLp
        (E := ℝ) 2 μ ℝ
        (∑ j : Fin 2, a j • specialUnitaryWilsonContinuousTwoModeSeed N j) =
      ∑ j : Fin 2, a j •
        specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
          (lt_of_lt_of_le (by norm_num) hN2) j := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_smul, specialUnitaryWilsonContinuousTwoModeSeed_toLp hN2 j]
    _ = specialUnitaryWilsonHaarTwoMode hN2 k := ha
    _ = ContinuousMap.toLp
        (E := ℝ) 2 μ ℝ
        (specialUnitaryWilsonContinuousTwoMode hN2 k) := by
          symm
          exact specialUnitaryWilsonContinuousTwoMode_toLp hN2 k

/-- Conversely every literal continuous seed belongs to the chosen continuous
two-mode span. -/
theorem specialUnitaryWilsonContinuousTwoModeSeed_mem_twoMode_span
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    specialUnitaryWilsonContinuousTwoModeSeed N k ∈
      Submodule.span ℝ
        (Set.range (specialUnitaryWilsonContinuousTwoMode hN2)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hL2 :=
    specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed_mem_twoMode_span hN2 k
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp hL2
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ?_
  refine ⟨a, ?_⟩
  apply
    (ContinuousMap.toLp_injective
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) μ)
  calc
    ContinuousMap.toLp
        (E := ℝ) 2 μ ℝ
        (∑ j : Fin 2, a j • specialUnitaryWilsonContinuousTwoMode hN2 j) =
      ∑ j : Fin 2, a j • specialUnitaryWilsonHaarTwoMode hN2 j := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_smul, specialUnitaryWilsonContinuousTwoMode_toLp hN2 j]
    _ = specialUnitaryWilsonPlaquetteEnergyHaarTwoModeSeed
        (lt_of_lt_of_le (by norm_num) hN2) k := ha
    _ = ContinuousMap.toLp
        (E := ℝ) 2 μ ℝ
        (specialUnitaryWilsonContinuousTwoModeSeed N k) := by
          symm
          exact specialUnitaryWilsonContinuousTwoModeSeed_toLp hN2 k

/-- Continuous representatives of the theorem-generated orthonormal two modes
span exactly the literal continuous seed pair `1,E_W`. -/
theorem specialUnitaryWilsonContinuousTwoMode_span_eq_seed
    {N : ℕ}
    (hN2 : 2 ≤ N) :
    Submodule.span ℝ
        (Set.range (specialUnitaryWilsonContinuousTwoMode hN2)) =
      Submodule.span ℝ
        (Set.range (specialUnitaryWilsonContinuousTwoModeSeed N)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact specialUnitaryWilsonContinuousTwoMode_mem_seed_span hN2 k
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact specialUnitaryWilsonContinuousTwoModeSeed_mem_twoMode_span hN2 k

/-- The literal SU(2) trace seed pair `1,r`, with
`r = normalized real trace = 1 - E_W`. -/
noncomputable def specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed :
    Fin 2 → C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ) :=
  ![(1 : C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ)),
    1 - specialUnitaryWilsonPlaquetteEnergyContinuous 2]

/-- The literal Wilson-energy seed span equals the literal normalized-trace
seed span in SU(2). -/
theorem specialUnitaryWilsonContinuousTwoModeSeed_two_span_eq_normalizedTraceSeed :
    Submodule.span ℝ
        (Set.range (specialUnitaryWilsonContinuousTwoModeSeed 2)) =
      Submodule.span ℝ
        (Set.range specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨0, by
        simp [specialUnitaryWilsonContinuousTwoModeSeed,
          specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed]⟩
    · have h0 :
          (1 : C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ)) ∈
            Submodule.span ℝ
              (Set.range specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed) := by
        exact Submodule.subset_span ⟨0, by
          simp [specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed]⟩
      have h1 :
          1 - specialUnitaryWilsonPlaquetteEnergyContinuous 2 ∈
            Submodule.span ℝ
              (Set.range specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed) := by
        exact Submodule.subset_span ⟨1, by
          simp [specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed]⟩
      simpa [specialUnitaryWilsonContinuousTwoModeSeed] using
        Submodule.sub_mem _ h0 h1
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨0, by
        simp [specialUnitaryWilsonContinuousTwoModeSeed,
          specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed]⟩
    · have h0 :
          (1 : C(Matrix.specialUnitaryGroup (Fin 2) ℂ, ℝ)) ∈
            Submodule.span ℝ
              (Set.range (specialUnitaryWilsonContinuousTwoModeSeed 2)) := by
        exact Submodule.subset_span ⟨0, by
          simp [specialUnitaryWilsonContinuousTwoModeSeed]⟩
      have h1 :
          specialUnitaryWilsonPlaquetteEnergyContinuous 2 ∈
            Submodule.span ℝ
              (Set.range (specialUnitaryWilsonContinuousTwoModeSeed 2)) := by
        exact Submodule.subset_span ⟨1, by
          simp [specialUnitaryWilsonContinuousTwoModeSeed]⟩
      simpa [specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed] using
        Submodule.sub_mem _ h0 h1

/-- In SU(2), the chosen continuous orthonormal two-mode representatives span
exactly the literal normalized-trace pair `1,r`. -/
theorem specialUnitaryWilsonContinuousTwoMode_two_span_eq_normalizedTraceSeed :
    Submodule.span ℝ
        (Set.range
          (specialUnitaryWilsonContinuousTwoMode
            (by norm_num : 2 ≤ (2 : ℕ)))) =
      Submodule.span ℝ
        (Set.range specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed) := by
  rw [specialUnitaryWilsonContinuousTwoMode_span_eq_seed
    (by norm_num : 2 ≤ (2 : ℕ))]
  exact specialUnitaryWilsonContinuousTwoModeSeed_two_span_eq_normalizedTraceSeed

/-- Each chosen SU(2) continuous two-mode representative has literal
normalized-trace coefficients. -/
theorem specialUnitaryWilsonContinuousTwoMode_two_exists_normalizedTrace_coefficients
    (k : Fin 2) :
    ∃ a : Fin 2 → ℝ,
      ∑ j : Fin 2,
          a j • specialUnitaryTwoNormalizedTraceContinuousTwoModeSeed j =
        specialUnitaryWilsonContinuousTwoMode
          (by norm_num : 2 ≤ (2 : ℕ)) k := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
  rw [← specialUnitaryWilsonContinuousTwoMode_two_span_eq_normalizedTraceSeed]
  exact Submodule.subset_span (Set.mem_range_self k)

end

end MathlibAnalytic
end MGAP4D
