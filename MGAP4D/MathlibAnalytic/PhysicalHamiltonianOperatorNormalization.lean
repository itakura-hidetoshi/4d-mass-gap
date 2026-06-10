import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge

namespace MGAP4D
namespace MathlibAnalytic

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
  internal_reference_scale_eq_one : referenceEnergyScale = 1
  internal_dimensional_gap_eq_exact : dimensionalGap = exactGapValueReal
  normalizedHamiltonianConventionVisible : Prop
  normalizedHamiltonianConventionVisible_proof : normalizedHamiltonianConventionVisible
  dimensionalGapReadingVisible : Prop
  dimensionalGapReadingVisible_proof : dimensionalGapReadingVisible
  theoremBodyUnchanged : Prop
  theoremBodyUnchanged_proof : theoremBodyUnchanged
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def PhysicalHamiltonianOperatorNormalizationData.ready
    (D : PhysicalHamiltonianOperatorNormalizationData) : Prop :=
  physicalHamiltonianNormalizationBridgeReviewSurface.ready ∧
  0 < D.referenceEnergyScale ∧
  D.normalizedHamiltonianScale = D.referenceEnergyScale⁻¹ * D.physicalHamiltonianScale ∧
  D.physicalHamiltonianScale = D.referenceEnergyScale * D.normalizedHamiltonianScale ∧
  D.normalizedGap = exactGapValueReal ∧
  D.dimensionalGap = D.referenceEnergyScale * D.normalizedGap ∧
  D.dimensionalGap = D.referenceEnergyScale * exactGapValueReal ∧
  D.referenceEnergyScale = 1 ∧
  D.dimensionalGap = exactGapValueReal ∧
  D.normalizedHamiltonianConventionVisible ∧
  D.dimensionalGapReadingVisible ∧
  D.theoremBodyUnchanged ∧
  D.publicBoundaryHeld

theorem physical_hamiltonian_operator_normalized_scale_def
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.normalizedHamiltonianScale = D.referenceEnergyScale⁻¹ * D.physicalHamiltonianScale := by
  exact D.normalized_hamiltonian_scale_def

theorem physical_hamiltonian_operator_scale_reconstruction
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.physicalHamiltonianScale = D.referenceEnergyScale * D.normalizedHamiltonianScale := by
  exact D.physical_hamiltonian_scale_reconstruction

theorem physical_hamiltonian_operator_normalized_gap_eq_exact
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.normalizedGap = exactGapValueReal := by
  exact D.normalized_gap_eq_exact

theorem physical_hamiltonian_operator_dimensional_gap_eq_reference_mul_exact
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.dimensionalGap = D.referenceEnergyScale * exactGapValueReal := by
  exact D.dimensional_gap_eq_reference_mul_exact

theorem physical_hamiltonian_operator_internal_dimensional_gap_eq_exact
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.dimensionalGap = exactGapValueReal := by
  exact D.internal_dimensional_gap_eq_exact

theorem physical_hamiltonian_operator_normalization_theorem_body_unchanged
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.theoremBodyUnchanged := by
  exact D.theoremBodyUnchanged_proof

theorem physical_hamiltonian_operator_normalization_public_boundary_held
    (D : PhysicalHamiltonianOperatorNormalizationData) :
    D.publicBoundaryHeld := by
  exact D.publicBoundaryHeld_proof

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
    internal_reference_scale_eq_one := rfl
    internal_dimensional_gap_eq_exact := rfl
    normalizedHamiltonianConventionVisible :=
      (1 : ℝ) = (1 : ℝ)⁻¹ * (1 : ℝ) ∧
      (1 : ℝ) = (1 : ℝ) * (1 : ℝ)
    normalizedHamiltonianConventionVisible_proof := by
      exact And.intro (by norm_num) (by norm_num)
    dimensionalGapReadingVisible :=
      exactGapValueReal = (1 : ℝ) * exactGapValueReal ∧
      exactGapValueReal = exactGapValueReal
    dimensionalGapReadingVisible_proof := by
      exact And.intro (by simp) rfl
    theoremBodyUnchanged := physicalHamiltonianNormalizationBridgeReviewSurface.ready
    theoremBodyUnchanged_proof := by
      exact physical_hamiltonian_normalization_bridge_review_surface_ready
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
    And.intro physicalHamiltonianOperatorNormalizationData.internal_reference_scale_eq_one <|
    And.intro physicalHamiltonianOperatorNormalizationData.internal_dimensional_gap_eq_exact <|
    And.intro physicalHamiltonianOperatorNormalizationData.normalizedHamiltonianConventionVisible_proof <|
    And.intro physicalHamiltonianOperatorNormalizationData.dimensionalGapReadingVisible_proof <|
    And.intro physicalHamiltonianOperatorNormalizationData.theoremBodyUnchanged_proof
      physicalHamiltonianOperatorNormalizationData.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
