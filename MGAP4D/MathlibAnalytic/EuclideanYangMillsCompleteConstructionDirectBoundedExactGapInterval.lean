import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerRootAPI
import MGAP4D.MathlibAnalytic.EuclideanYangMillsVacuumOrthogonalGapBridge
import MGAP4D.MathlibAnalytic.WightmanOSHamiltonianGapSpectrumTheorems
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Exact spectral-gap interval consequences for the complete Yang--Mills direct
bounded construction route.

This file specializes the general mathlib-facing Hamiltonian gap theorems to the
complete construction spine.  It identifies `exactGapValueReal` as the least
nonzero spectral value and proves that the open interval between the vacuum and
that exact threshold contains no spectral point.

It does not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.  Every result is parametrized by the existing complete
construction spine.
-/

/-- The complete construction spine carries the exact Hamiltonian mass-gap
predicate at `exactGapValueReal`. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    HasHamiltonianMassGap
      S.definitionBridge.spine.model.energySpectrum exactGapValueReal := by
  exact os_wightman_reconstruction_spine_exact_hasHamiltonianMassGap
    S.definitionBridge.spine

/-- The complete energy spectrum lies in the vacuum point or above the exact gap. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_subset_vacuum_union_exactGapRay
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum ⊆
      ({0} : Set ℝ) ∪ Set.Ici exactGapValueReal := by
  exact hasHamiltonianMassGap_spectrum_subset
    (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S)

/-- The vacuum is isolated by the exact open spectral-gap interval. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_vacuum_exactGapInterval_empty
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Set.Ioo 0 exactGapValueReal ∩
      S.definitionBridge.spine.model.energySpectrum = ∅ := by
  exact hasHamiltonianMassGap_vacuum_isolated
    (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S)

/-- The exact gap value is attained in the complete construction spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal ∈ S.definitionBridge.spine.model.energySpectrum := by
  exact os_wightman_reconstruction_spine_exact_gap_mem_energySpectrum
    S.definitionBridge.spine

/-- The exact gap value is the least point of the nonzero energy spectrum. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      exactGapValueReal := by
  exact hasHamiltonianMassGap_isLeast_nonvacuum
    (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S)
    (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum S)

/-- Every nonzero spectral value lies in the closed ray above the exact gap. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_exactGapRay
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
      Set.Ici exactGapValueReal := by
  intro E hE
  exact
    (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S).2 hE

/-- The nonzero-spectrum infimum is the attained exact gap value. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_sInf_eq_exactGap
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) =
      exactGapValueReal := by
  exact hasHamiltonianMassGap_sInf_nonvacuum_eq
    (euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S)
    (euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum S)

/-- Exact-gap formula in the orientation used by the public consumer API. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGap_eq_nonzeroSpectrum_sInf
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    exactGapValueReal =
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact
    (euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_sInf_eq_exactGap S).symm

end

end MathlibAnalytic
end MGAP4D
