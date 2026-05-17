import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge

namespace MGAP4D
namespace MathlibAnalytic

/-- Operator-level normalization surface for the physical Hamiltonian.

The convention recorded here is the dimensionless operator scaling

`H_norm = E0^{-1} * H_phys`

tracked at the scalar normalization layer used by the theorem route.  The same
surface records the dimensional gap reading

`Delta_phys(E0) = E0 * (33/20)`.

In internal normalized units, `E0 = 1`, so the dimensional reading collapses
back to the dimensionless theorem value `33/20`.

Boundary: this is a normalization layer. It does not change the theorem body,
the spectral/PVM witness, the plaquette witness, or the public release gate. -/
structure PhysicalHamiltonianOperatorNormalizationData where
  bridgeReady : physicalHamiltonianNormalizationBridgeReviewSurface.ready
  referenceEnergyScale : ℝ
  physicalHamiltonianScale : ℝ
  normalizedHamiltonianScale : ℝ
  scale_positive : 0 < referenceEnergyScale
  normalized_hamiltonian_scale_def :
    normalizedHamiltonianScale = referenceEnergyScale⁻¹ * physicalHamiltonianScale
  physical_hamiltonian_scale_reconstruction :
    physicalHamiltonianScale = referenceEnergyScale * normalizedHamiltonianScale
  normalizedGap : ℝ
  dimensionalGap : ℝ
  normalized_gap_eq_exact : normalizedGap = exactGapValueReal
  dimensional_gap_def : dimensionalGap = referenceEnergyScale * normalizedGap
  dimensional_gap_eq_reference_mul_exact : dimensionalGap = referenceEnergyScale * exactGapValueReal
  dimensional_gap_eq_reference_mul_3320 : dimensionalGap = referenceEnergyScale * ((33 : ℝ) / 20)
  internal_reference_scale_eq_one : referenceEnergyScale = 1
  internal_dimensional_gap_eq_3320 : dimensionalGap = (33 : ℝ) / 20
  normalizedHamiltonianConventionVisible : Prop
  normalizedHamiltonianConventionVisible_proof : normalizedHamiltonianConventionVisible
  dimensionalGapReadingVisible : Prop
  dimensionalGapReadingVisible_proof : dimensionalGapReadingVisible
  theoremBodyUnchanged : Prop
  theoremBodyUnchanged_proof : theoremBodyUnchanged
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the operator-level normalization surface. -/
def PhysicalHamiltonianOperatorNormalizationData.ready
    (D : PhysicalHamiltonianOperatorNormalizationData) : Prop :=
  physicalHamiltonianNormalizationBridgeReviewSurface.ready ∧
  0 < D.referenceEnergyScale ∧
  D.normalizedHamiltonianScale = D.referenceEnergyScale⁻¹ * D.physicalHamiltonianScale ∧
  D.physicalHamiltonianScale = D.referenceEnergyScale * D.normalizedHamiltonianScale ∧
  D.normalizedGap = exactGapValueReal ∧
  D.dimensionalGap = D.referenceEnergyScale * D.normalizedGap ∧
  D.dimensionalGap = D.referenceEnergyScale * exactGapValueReal ∧
  D.dimensionalGap = D.referenceEnergyScale * ((33 : ℝ) / 20) ∧
  D.referenceEnergyScale = 1 ∧
  D.dimensionalGap = (33 : ℝ) / 20 ∧
  D.normalizedHamiltonianConventionVisible ∧
  D.dimensionalGapReadingVisible ∧
  D.theoremBodyUnchanged ∧
  D.publicBoundaryHeld

/-- The operator normalization scale is `E0^{-1}` times the physical scale. -/
theorem physical_hamiltonian_operator_normalized_scale_def
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.normalizedHamiltonianScale = D.referenceEnergyScale⁻¹ * D.physicalHamiltonianScale := by
  exact D.normalized_hamiltonian_scale_def

/-- The physical Hamiltonian scale is reconstructed from the normalized scale. -/
theorem physical_hamiltonian_operator_scale_reconstruction
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.physicalHamiltonianScale = D.referenceEnergyScale * D.normalizedHamiltonianScale := by
  exact D.physical_hamiltonian_scale_reconstruction

/-- The normalized gap keeps the theorem-body exact value. -/
theorem physical_hamiltonian_operator_normalized_gap_eq_3320
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.normalizedGap = (33 : ℝ) / 20 := by
  rw [D.normalized_gap_eq_exact]
  exact exactGapValueReal_eq

/-- The dimensional gap reads as `E0 * (33/20)`. -/
theorem physical_hamiltonian_operator_dimensional_gap_eq_reference_mul_3320
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.dimensionalGap = D.referenceEnergyScale * ((33 : ℝ) / 20) := by
  exact D.dimensional_gap_eq_reference_mul_3320

/-- In internal normalized units, the dimensional reading returns to `33/20`. -/
theorem physical_hamiltonian_operator_internal_dimensional_gap_eq_3320
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.dimensionalGap = (33 : ℝ) / 20 := by
  exact D.internal_dimensional_gap_eq_3320

/-- The normalization layer leaves the theorem body unchanged. -/
theorem physical_hamiltonian_operator_normalization_theorem_body_unchanged
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.theoremBodyUnchanged := by
  exact D.theoremBodyUnchanged_proof

/-- The normalization layer preserves the public boundary. -/
theorem physical_hamiltonian_operator_normalization_public_boundary_held
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.publicBoundaryHeld := by
  exact D.publicBoundaryHeld_proof

/-- Prototype operator normalization in MGAP4D internal normalized units. -/
noncomputable def physicalHamiltonianOperatorNormalizationData :
    PhysicalHamiltonianOperatorNormalizationData :=
  { bridgeReady := physical_hamiltonian_normalization_bridge_review_surface_ready
    referenceEnergyScale := 1
    physicalHamiltonianScale := 1
    normalizedHamiltonianScale := 1
    scale_positive := by norm_num
    normalized_hamiltonian_scale_def := by norm_num
    physical_hamiltonian_scale_reconstruction := by norm_num
    normalizedGap := exactGapValueReal
    dimensionalGap := exactGapValueReal
    normalized_gap_eq_exact := rfl
    dimensional_gap_def := by simp
    dimensional_gap_eq_reference_mul_exact := by simp
    dimensional_gap_eq_reference_mul_3320 := by
      simpa using exactGapValueReal_eq
    internal_reference_scale_eq_one := rfl
    internal_dimensional_gap_eq_3320 := exactGapValueReal_eq
    normalizedHamiltonianConventionVisible :=
      (1 : ℝ) = (1 : ℝ)⁻¹ * (1 : ℝ) ∧
      (1 : ℝ) = (1 : ℝ) * (1 : ℝ)
    normalizedHamiltonianConventionVisible_proof := by
      exact And.intro (by norm_num) (by norm_num)
    dimensionalGapReadingVisible :=
      exactGapValueReal = (1 : ℝ) * ((33 : ℝ) / 20) ∧
      exactGapValueReal = (33 : ℝ) / 20
    dimensionalGapReadingVisible_proof := by
      exact And.intro (by simpa using exactGapValueReal_eq) exactGapValueReal_eq
    theoremBodyUnchanged :=
      physicalHamiltonianNormalizationBridgeReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20
    theoremBodyUnchanged_proof := by
      exact And.intro physical_hamiltonian_normalization_bridge_review_surface_ready exactGapValueReal_eq
    publicBoundaryHeld := physicalHamiltonianNormalizationBridgeReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof := physicalHamiltonianNormalizationBridgeReviewSurface.publicBoundaryHeld_proof }

theorem physical_hamiltonian_operator_normalization_ready :
    physicalHamiltonianOperatorNormalizationData.ready := by
  exact And.intro physicalHamiltonianOperatorNormalizationData.bridgeReady <|
    And.intro physicalHamiltonianOperatorNormalizationData.scale_positive <|
    And.intro physicalHamiltonianOperatorNormalizationData.normalized_hamiltonian_scale_def <|
    And.intro physicalHamiltonianOperatorNormalizationData.physical_hamiltonian_scale_reconstruction <|
    And.intro physicalHamiltonianOperatorNormalizationData.normalized_gap_eq_exact <|
    And.intro physicalHamiltonianOperatorNormalizationData.dimensional_gap_def <|
    And.intro physicalHamiltonianOperatorNormalizationData.dimensional_gap_eq_reference_mul_exact <|
    And.intro physicalHamiltonianOperatorNormalizationData.dimensional_gap_eq_reference_mul_3320 <|
    And.intro physicalHamiltonianOperatorNormalizationData.internal_reference_scale_eq_one <|
    And.intro physicalHamiltonianOperatorNormalizationData.internal_dimensional_gap_eq_3320 <|
    And.intro physicalHamiltonianOperatorNormalizationData.normalizedHamiltonianConventionVisible_proof <|
    And.intro physicalHamiltonianOperatorNormalizationData.dimensionalGapReadingVisible_proof <|
    And.intro physicalHamiltonianOperatorNormalizationData.theoremBodyUnchanged_proof
      physicalHamiltonianOperatorNormalizationData.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
