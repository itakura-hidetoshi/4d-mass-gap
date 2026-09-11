import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedExactGapInterval
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Certificate package for the exact spectral-gap interval of the complete
Yang--Mills direct bounded construction route.

The certificate combines the exact Hamiltonian mass-gap predicate, vacuum
isolation, attainment and leastness of the exact threshold, the infimum
identity, and the compact root consumer API.

It does not assert an unconditional Yang--Mills construction or a final Clay
mass-gap theorem.
-/

/-- Exact spectral-gap interval certificate attached to the complete construction
spine. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  hamiltonianGap :
    HasHamiltonianMassGap
      S.definitionBridge.spine.model.energySpectrum exactGapValueReal
  spectrumSubset :
    S.definitionBridge.spine.model.energySpectrum ⊆
      ({0} : Set ℝ) ∪ Set.Ici exactGapValueReal
  vacuumIsolated :
    Set.Ioo 0 exactGapValueReal ∩
      S.definitionBridge.spine.model.energySpectrum = ∅
  exactGapMem :
    exactGapValueReal ∈ S.definitionBridge.spine.model.energySpectrum
  exactGapLeast :
    IsLeast
      (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
      exactGapValueReal
  nonzeroSpectrumSubset :
    S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
      Set.Ici exactGapValueReal
  sInfEq :
    sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) =
      exactGapValueReal
  rootConsumerAPI :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S

/-- Canonical exact spectral-gap interval certificate for the complete construction
spine. -/
def euclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate S where
  hamiltonianGap :=
    euclideanYangMillsCompleteConstructionDirectBounded_exactHamiltonianMassGap S
  spectrumSubset :=
    euclideanYangMillsCompleteConstructionDirectBounded_energySpectrum_subset_vacuum_union_exactGapRay S
  vacuumIsolated :=
    euclideanYangMillsCompleteConstructionDirectBounded_vacuum_exactGapInterval_empty S
  exactGapMem :=
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_mem_energySpectrum S
  exactGapLeast :=
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_isLeast_nonzeroSpectrum S
  nonzeroSpectrumSubset :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_subset_exactGapRay S
  sInfEq :=
    euclideanYangMillsCompleteConstructionDirectBounded_nonzeroSpectrum_sInf_eq_exactGap S
  rootConsumerAPI :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPI S

/-- Compact proposition exposed by the exact-gap interval certificate. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificateProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    0 < exactGapValueReal ∧
      Set.Ioo 0 exactGapValueReal ∩
        S.definitionBridge.spine.model.energySpectrum = ∅ ∧
      IsLeast
        (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ))
        exactGapValueReal ∧
      S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootAPIProp S

/-- Compact theorem exposed by the exact-gap interval certificate. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificateProp S := by
  let C :=
    euclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate S
  exact ⟨
    C.hamiltonianGap.1,
    C.vacuumIsolated,
    C.exactGapLeast,
    C.nonzeroSpectrumSubset,
    C.sInfEq,
    C.rootConsumerAPI⟩

/-- Complete exact-gap endpoint including both orientations of the infimum formula. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificateProp S ∧
      exactGapValueReal =
        sInf (S.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)) := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate S,
    euclideanYangMillsCompleteConstructionDirectBounded_exactGap_eq_nonzeroSpectrum_sInf S⟩

end

end MathlibAnalytic
end MGAP4D
