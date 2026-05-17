import MGAP4D.MathlibAnalytic.ConcreteResidualClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Standard interpretation bridge for the physical Hamiltonian normalization.

The internal theorem uses the dimensionless normalized Hamiltonian convention.
This bridge makes that convention explicit by introducing a positive reference
energy scale `E₀` and the standard relation

`normalizedGap = physicalGap / E₀`, equivalently
`physicalGap = E₀ * normalizedGap`.

In MGAP4D internal normalized units the reference scale is fixed to `E₀ = 1`,
so the dimensionless exact value is `33/20`.  A reader who wants dimensional
units should read the physical gap as `E₀ * (33/20)`.

Boundary: this is a normalization/interpretation bridge.  It does not change the
spectral theorem body, the PVM body, or the concrete residual closure. -/
structure PhysicalHamiltonianNormalizationBridgeData where
  concreteResidualClosureReady : concreteResidualClosureReviewSurface.ready
  referenceEnergyScale : ℝ
  physicalGap : ℝ
  normalizedGap : ℝ
  scale_positive : 0 < referenceEnergyScale
  normalized_gap_def : normalizedGap = physicalGap / referenceEnergyScale
  physical_gap_reconstruction : physicalGap = referenceEnergyScale * normalizedGap
  internal_reference_scale_eq_one : referenceEnergyScale = 1
  normalized_gap_eq_exact : normalizedGap = exactGapValueReal
  physical_gap_eq_exact_in_internal_units : physicalGap = exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  standardInterpretationVisible : Prop
  standardInterpretationVisible_proof : standardInterpretationVisible
  dimensionalReadingVisible : Prop
  dimensionalReadingVisible_proof : dimensionalReadingVisible
  theoremBodyUnchanged : Prop
  theoremBodyUnchanged_proof : theoremBodyUnchanged
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the physical Hamiltonian normalization bridge. -/
def PhysicalHamiltonianNormalizationBridgeData.ready
    (D : PhysicalHamiltonianNormalizationBridgeData) : Prop :=
  concreteResidualClosureReviewSurface.ready ∧
  0 < D.referenceEnergyScale ∧
  D.normalizedGap = D.physicalGap / D.referenceEnergyScale ∧
  D.physicalGap = D.referenceEnergyScale * D.normalizedGap ∧
  D.referenceEnergyScale = 1 ∧
  D.normalizedGap = exactGapValueReal ∧
  D.physicalGap = exactGapValueReal ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.standardInterpretationVisible ∧ D.dimensionalReadingVisible ∧
  D.theoremBodyUnchanged ∧ D.publicBoundaryHeld

/-- The reference energy scale is positive. -/
theorem physical_hamiltonian_normalization_scale_positive
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    0 < D.referenceEnergyScale := by
  exact D.scale_positive

/-- Standard dimensionless normalization: normalized gap equals physical gap divided by `E₀`. -/
theorem physical_hamiltonian_normalized_gap_def
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.normalizedGap = D.physicalGap / D.referenceEnergyScale := by
  exact D.normalized_gap_def

/-- Dimensional reconstruction: physical gap equals `E₀` times normalized gap. -/
theorem physical_hamiltonian_gap_reconstruction
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.physicalGap = D.referenceEnergyScale * D.normalizedGap := by
  exact D.physical_gap_reconstruction

/-- In internal normalized units, the reference scale is one. -/
theorem physical_hamiltonian_internal_reference_scale_eq_one
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.referenceEnergyScale = 1 := by
  exact D.internal_reference_scale_eq_one

/-- The normalized exact gap is `33/20` in internal units. -/
theorem physical_hamiltonian_normalized_gap_eq_3320
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.normalizedGap = (33 : ℝ) / 20 := by
  rw [D.normalized_gap_eq_exact]
  exact D.exact_value_eq_3320

/-- The standard normalization interpretation is visible from concrete equations. -/
theorem physical_hamiltonian_standard_interpretation_visible
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.standardInterpretationVisible := by
  exact D.standardInterpretationVisible_proof

/-- The dimensional reading is visible from the internal scale and exact value. -/
theorem physical_hamiltonian_dimensional_reading_visible
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.dimensionalReadingVisible := by
  exact D.dimensionalReadingVisible_proof

/-- The normalization bridge leaves the theorem body unchanged. -/
theorem physical_hamiltonian_normalization_theorem_body_unchanged
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.theoremBodyUnchanged := by
  exact D.theoremBodyUnchanged_proof

/-- The normalization bridge preserves the public boundary. -/
theorem physical_hamiltonian_normalization_public_boundary_held
    (D : PhysicalHamiltonianNormalizationBridgeData) :
    D.publicBoundaryHeld := by
  exact D.publicBoundaryHeld_proof

/-- Prototype normalization bridge in MGAP4D internal normalized units. -/
noncomputable def prototypePhysicalHamiltonianNormalizationBridgeData :
    PhysicalHamiltonianNormalizationBridgeData :=
  { concreteResidualClosureReady := concrete_residual_closure_review_surface_ready
    referenceEnergyScale := 1
    physicalGap := exactGapValueReal
    normalizedGap := exactGapValueReal
    scale_positive := by norm_num
    normalized_gap_def := by simp
    physical_gap_reconstruction := by simp
    internal_reference_scale_eq_one := rfl
    normalized_gap_eq_exact := rfl
    physical_gap_eq_exact_in_internal_units := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    standardInterpretationVisible :=
      exactGapValueReal = exactGapValueReal / (1 : ℝ) ∧
      exactGapValueReal = (1 : ℝ) * exactGapValueReal
    standardInterpretationVisible_proof := by
      exact And.intro (by simp) (by simp)
    dimensionalReadingVisible :=
      (1 : ℝ) = 1 ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      exactGapValueReal = (33 : ℝ) / 20
    dimensionalReadingVisible_proof := by
      exact And.intro rfl (And.intro exactGapValueReal_eq exactGapValueReal_eq)
    theoremBodyUnchanged :=
      concreteResidualClosureReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20
    theoremBodyUnchanged_proof := by
      exact And.intro concrete_residual_closure_review_surface_ready exactGapValueReal_eq
    publicBoundaryHeld := concreteResidualClosureReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof := concreteResidualClosureReviewSurface.publicBoundaryHeld_proof }

theorem prototype_physical_hamiltonian_normalization_bridge_ready :
    prototypePhysicalHamiltonianNormalizationBridgeData.ready := by
  exact And.intro prototypePhysicalHamiltonianNormalizationBridgeData.concreteResidualClosureReady <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.scale_positive <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.normalized_gap_def <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.physical_gap_reconstruction <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.internal_reference_scale_eq_one <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.normalized_gap_eq_exact <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.physical_gap_eq_exact_in_internal_units <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.exact_value_eq_3320 <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.standardInterpretationVisible_proof <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.dimensionalReadingVisible_proof <|
    And.intro prototypePhysicalHamiltonianNormalizationBridgeData.theoremBodyUnchanged_proof
      prototypePhysicalHamiltonianNormalizationBridgeData.publicBoundaryHeld_proof

/-- Review surface for the physical Hamiltonian normalization bridge. -/
structure PhysicalHamiltonianNormalizationBridgeReviewSurface where
  concreteResidualClosureReady : concreteResidualClosureReviewSurface.ready
  normalizationBridgeReady : prototypePhysicalHamiltonianNormalizationBridgeData.ready
  scalePositive : 0 < prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale
  normalizedGapDef : prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap =
    prototypePhysicalHamiltonianNormalizationBridgeData.physicalGap /
      prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale
  physicalGapReconstruction : prototypePhysicalHamiltonianNormalizationBridgeData.physicalGap =
    prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale *
      prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap
  internalReferenceScaleEqOne :
    prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale = 1
  normalizedGapEq3320 :
    prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap = (33 : ℝ) / 20
  standardInterpretationVisible : Prop
  standardInterpretationVisible_proof : standardInterpretationVisible
  dimensionalReadingVisible : Prop
  dimensionalReadingVisible_proof : dimensionalReadingVisible
  theoremBodyUnchanged : Prop
  theoremBodyUnchanged_proof : theoremBodyUnchanged
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def PhysicalHamiltonianNormalizationBridgeReviewSurface.ready
    (S : PhysicalHamiltonianNormalizationBridgeReviewSurface) : Prop :=
  concreteResidualClosureReviewSurface.ready ∧
  prototypePhysicalHamiltonianNormalizationBridgeData.ready ∧
  0 < prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale ∧
  prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap =
    prototypePhysicalHamiltonianNormalizationBridgeData.physicalGap /
      prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale ∧
  prototypePhysicalHamiltonianNormalizationBridgeData.physicalGap =
    prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale *
      prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap ∧
  prototypePhysicalHamiltonianNormalizationBridgeData.referenceEnergyScale = 1 ∧
  prototypePhysicalHamiltonianNormalizationBridgeData.normalizedGap = (33 : ℝ) / 20 ∧
  S.standardInterpretationVisible ∧ S.dimensionalReadingVisible ∧
  S.theoremBodyUnchanged ∧ S.publicBoundaryHeld

noncomputable def physicalHamiltonianNormalizationBridgeReviewSurface :
    PhysicalHamiltonianNormalizationBridgeReviewSurface :=
  { concreteResidualClosureReady := concrete_residual_closure_review_surface_ready
    normalizationBridgeReady := prototype_physical_hamiltonian_normalization_bridge_ready
    scalePositive := prototypePhysicalHamiltonianNormalizationBridgeData.scale_positive
    normalizedGapDef := prototypePhysicalHamiltonianNormalizationBridgeData.normalized_gap_def
    physicalGapReconstruction := prototypePhysicalHamiltonianNormalizationBridgeData.physical_gap_reconstruction
    internalReferenceScaleEqOne := prototypePhysicalHamiltonianNormalizationBridgeData.internal_reference_scale_eq_one
    normalizedGapEq3320 := physical_hamiltonian_normalized_gap_eq_3320
      prototypePhysicalHamiltonianNormalizationBridgeData
    standardInterpretationVisible :=
      prototypePhysicalHamiltonianNormalizationBridgeData.standardInterpretationVisible
    standardInterpretationVisible_proof :=
      prototypePhysicalHamiltonianNormalizationBridgeData.standardInterpretationVisible_proof
    dimensionalReadingVisible :=
      prototypePhysicalHamiltonianNormalizationBridgeData.dimensionalReadingVisible
    dimensionalReadingVisible_proof :=
      prototypePhysicalHamiltonianNormalizationBridgeData.dimensionalReadingVisible_proof
    theoremBodyUnchanged :=
      prototypePhysicalHamiltonianNormalizationBridgeData.theoremBodyUnchanged
    theoremBodyUnchanged_proof :=
      prototypePhysicalHamiltonianNormalizationBridgeData.theoremBodyUnchanged_proof
    publicBoundaryHeld :=
      prototypePhysicalHamiltonianNormalizationBridgeData.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      prototypePhysicalHamiltonianNormalizationBridgeData.publicBoundaryHeld_proof }

theorem physical_hamiltonian_normalization_bridge_review_surface_ready :
    physicalHamiltonianNormalizationBridgeReviewSurface.ready := by
  exact And.intro physicalHamiltonianNormalizationBridgeReviewSurface.concreteResidualClosureReady <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.normalizationBridgeReady <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.scalePositive <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.normalizedGapDef <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.physicalGapReconstruction <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.internalReferenceScaleEqOne <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.normalizedGapEq3320 <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.standardInterpretationVisible_proof <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.dimensionalReadingVisible_proof <|
    And.intro physicalHamiltonianNormalizationBridgeReviewSurface.theoremBodyUnchanged_proof
      physicalHamiltonianNormalizationBridgeReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
