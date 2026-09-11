import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureExactGapConstructionSpine
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedUniqueMassGapWitnessCertificate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Theorem package for the dependency-reduced exact-gap continuum construction
spine.

The reduced spine converts to the existing construction spine, so the complete
Mathlib-facing spectral theorem chain remains available without independently
supplying positive energy, vacuum isolation, first excitation, mass-gap values,
or repeated Hamiltonian/PVM theorem fields.
-/

/-- The reduced exact-gap continuum spine induces readiness of the existing
continuum construction spine. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_fullLimitReady
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.limitReady := by
  exact euclidean_yang_mills_continuum_spine_limit_ready S.toConstructionSpine

/-- The reduced exact-gap continuum spine induces the model-level mass-gap
predicate through the existing construction route. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_hasMassGap
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.hasMassGap := by
  exact euclidean_yang_mills_continuum_spine_mass_gap_definition
    S.toConstructionSpine

/-- The reduced exact-gap continuum spine exposes exact-gap positivity. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapPositive
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    0 < exactGapValueReal := by
  exact S.definitionBridge.spine.spectralCore.exactHamiltonianMassGap.1

/-- The reduced exact-gap continuum spine identifies the exact gap with the
nonzero-spectrum infimum of the generated full model. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapThreshold
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    exactGapValueReal =
      sInf
        (S.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
          ({0} : Set ℝ)) := by
  exact euclidean_yang_mills_continuum_spine_definition_bridge_nonvacuum_threshold
    S.toConstructionSpine

/-- The generated full model first excitation is exactly the reduced exact gap. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_firstExcitationEqExactGap
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.firstExcitation =
      exactGapValueReal := by
  rfl

/-- The generated displayed mass-gap value is exactly the reduced exact gap. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_massGapValueEqExactGap
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.massGapValue =
      exactGapValueReal := by
  rfl

/-- The reduced exact-gap continuum spine detects the attained exact gap through
the generated spectral PVM. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapPVMDetected
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    ∃ ψ : S.toConstructionSpine.definitionBridge.spine.model.H,
      ψ ∈ S.toConstructionSpine.definitionBridge.spine.model.spectralPVM
        ({exactGapValueReal} : Set ℝ) := by
  exact S.definitionBridge.exactGapPVMDetected

/-- The generated full model has the exact gap as the least nonzero spectral
energy. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapIsLeast
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    IsLeast
      (S.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
        ({0} : Set ℝ))
      exactGapValueReal := by
  exact S.definitionBridge.spine.spectralCore.exactGapIsLeast

/-- The reduced construction spine inherits the exact-threshold spectral
classification through the generated full construction spine. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactThresholdSeparation
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      S.toConstructionSpine := by
  exact
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation
      S.toConstructionSpine

/-- The reduced construction spine inherits uniqueness of the canonical mass-gap
witness through the generated full construction spine. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_uniqueMassGapWitness
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
      S.toConstructionSpine := by
  exact
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessCertificate
      S.toConstructionSpine

/-- Certificate for the reduced continuum construction route and all generated
spectral consequences. -/
structure EuclideanYangMillsContinuumMeasureExactGapConstructionSpineCertificate
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) where
  reducedLimitReady : S.limitReady
  fullLimitReady : S.toConstructionSpine.limitReady
  massGap : S.toConstructionSpine.definitionBridge.spine.model.hasMassGap
  exactGapPositive : 0 < exactGapValueReal
  exactGapThreshold :
    exactGapValueReal =
      sInf
        (S.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
          ({0} : Set ℝ))
  firstExcitationEqExactGap :
    S.toConstructionSpine.definitionBridge.spine.model.firstExcitation =
      exactGapValueReal
  massGapValueEqExactGap :
    S.toConstructionSpine.definitionBridge.spine.model.massGapValue =
      exactGapValueReal
  exactGapPVMDetected :
    ∃ ψ : S.toConstructionSpine.definitionBridge.spine.model.H,
      ψ ∈ S.toConstructionSpine.definitionBridge.spine.model.spectralPVM
        ({exactGapValueReal} : Set ℝ)
  exactGapLeast :
    IsLeast
      (S.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
        ({0} : Set ℝ))
      exactGapValueReal
  thresholdSeparation :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      S.toConstructionSpine
  uniqueMassGapWitness :
    euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
      S.toConstructionSpine

/-- Canonical certificate for the reduced continuum construction route. -/
def euclideanYangMillsContinuumMeasureExactGapConstructionSpineCertificate
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpineCertificate S where
  reducedLimitReady :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_limitReady S
  fullLimitReady :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_fullLimitReady S
  massGap :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_hasMassGap S
  exactGapPositive :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapPositive S
  exactGapThreshold :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapThreshold S
  firstExcitationEqExactGap :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_firstExcitationEqExactGap S
  massGapValueEqExactGap :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_massGapValueEqExactGap S
  exactGapPVMDetected :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapPVMDetected S
  exactGapLeast :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapIsLeast S
  thresholdSeparation :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactThresholdSeparation S
  uniqueMassGapWitness :=
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_uniqueMassGapWitness S

/-- Compact endpoint showing that the reduced continuum input surface generates
the full exact mass-gap theorem package. -/
theorem euclideanYangMillsContinuumMeasureExactGapConstructionSpine_complete
    (S : EuclideanYangMillsContinuumMeasureExactGapConstructionSpine) :
    S.toConstructionSpine.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal =
        sInf
          (S.toConstructionSpine.definitionBridge.spine.model.energySpectrum \
            ({0} : Set ℝ)) ∧
      S.toConstructionSpine.definitionBridge.spine.model.firstExcitation =
        exactGapValueReal ∧
      S.toConstructionSpine.definitionBridge.spine.model.massGapValue =
        exactGapValueReal ∧
      euclideanYangMillsCompleteConstructionDirectBounded_uniqueMassGapWitnessProp
        S.toConstructionSpine := by
  exact ⟨
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_hasMassGap S,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapPositive S,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactGapThreshold S,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_firstExcitationEqExactGap S,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_massGapValueEqExactGap S,
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_uniqueMassGapWitness S⟩

end

end MathlibAnalytic
end MGAP4D
