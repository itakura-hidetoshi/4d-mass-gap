import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorEvaluationReceipts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Fine orbit of a fine boundary configuration at one coarse-refinement step. -/
def finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteEvenFourTorusZ2ResidualGaugeOrbit
      (finiteEvenFourTorusDoubleRefinement H) :=
  finiteGroupOrbitClass
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) A

/-- Coarse orbit obtained from a fine configuration by the actual geometric
coarse map. -/
def finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteEvenFourTorusZ2ResidualGaugeOrbit H :=
  finiteGroupOrbitClass
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)

/-- Exact pointwise scalar relating the normalized invariant-carrier embedding
to raw pullback along the configuration coarse map.  It retains the orbit-mass
and probability factors explicitly; no cancellation of stabilizer or fibre
cardinalities is assumed. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) : ℝ :=
  let qf := finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration H A
  let qc := finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration H A
  (Real.sqrt
      ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement H)).weight qf) *
    (Real.sqrt
        (finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H) qc) /
      Real.sqrt
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight qc))) /
    Real.sqrt
      (finiteGroupOrbitMass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
          (finiteEvenFourTorusDoubleRefinement H))
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) qf)

/-- Every pointwise embedding scale is strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    0 < finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A := by
  let qf := finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration H A
  let qc := finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration H A
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
  dsimp only
  have hwf :
      0 < (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
        (finiteEvenFourTorusDoubleRefinement H)).weight qf :=
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
      (finiteEvenFourTorusDoubleRefinement H)).weight_pos qf
  have hwc :
      0 < (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight qc :=
    (finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight_pos qc
  have hmf :
      0 < finiteGroupOrbitMass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
          (finiteEvenFourTorusDoubleRefinement H))
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) qf :=
    finiteGroupOrbitMass_pos _ _ qf
  have hmc :
      0 < finiteGroupOrbitMass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) qc :=
    finiteGroupOrbitMass_pos _ _ qc
  exact div_pos
    (mul_pos (Real.sqrt_pos.2 hwf)
      (div_pos (Real.sqrt_pos.2 hmc) (Real.sqrt_pos.2 hwc)))
    (Real.sqrt_pos.2 hmf)

/-- In particular, the exact pointwise normalization factor never vanishes. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_ne_zero
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A ≠ 0 :=
  ne_of_gt
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos H A)

/-- Exact pointwise configuration formula for the canonical normalized
coarse-to-fine invariant Hilbert embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 A =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) := by
  let qf := finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration H A
  let qc := finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration H A
  have hcoarseClass :
      finiteEvenFourTorusZ2GaugeOrbitCoarseMap H qf = qc := by
    change
      finiteEvenFourTorusZ2GaugeOrbitCoarseMap H
          (finiteGroupOrbitClass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
              (finiteEvenFourTorusDoubleRefinement H))
            (FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)) A) =
        finiteGroupOrbitClass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)
    exact finiteEvenFourTorusZ2GaugeOrbitCoarseMap_class H A
  have hrep :
      f.1
          (finiteGroupOrbitRepresentative
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) qc) =
        f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) := by
    exact finiteGroupInvariant_value_eq_representative
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) f qc
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) rfl
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry_apply]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification_inverse_apply]
  rw [finiteEvenFourTorusZ2GaugeOrbitCoarseL2PullbackLinearIsometry_apply]
  rw [finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Identification_forward_apply]
  change
    (Real.sqrt
        ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data
          (finiteEvenFourTorusDoubleRefinement H)).weight qf) *
      ((Real.sqrt
          (finiteGroupOrbitMass
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) qc) *
          f.1
            (finiteGroupOrbitRepresentative
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H) qc)) /
        Real.sqrt
          ((finiteEvenFourTorusZ2GaugeOrbitProbabilityL2Data H).weight qc))) /
      Real.sqrt
        (finiteGroupOrbitMass
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
            (finiteEvenFourTorusDoubleRefinement H))
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) qf) = _
  rw [hrep]
  unfold finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
  dsimp only
  ring

/-- The raw configuration pullback differs from the canonical invariant
embedding only by the explicit nonzero pointwise normalization factor. -/
theorem finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullback_eq_scale_inv_mul_embedding
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H f).1 A =
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A)⁻¹ *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 A := by
  rw [finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap_apply]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  field_simp [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_ne_zero]

/-- Audit-visible exact normalization package for the actual invariant
cross-volume embedding. -/
structure Z2GaugeInvariantCrossVolumeEmbeddingNormalizationPackage (H : ℕ) where
  scale :
    FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H) → ℝ
  scale_eq : scale = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H
  scale_pos : ∀ A, 0 < scale A
  normalizedFormula : ∀ f A,
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 A =
      scale A * f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)
  rawFormula : ∀ f A,
    (finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullbackLinearMap H f).1 A =
      (scale A)⁻¹ *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 A

/-- Construct the complete actual embedding-normalization receipt. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantCrossVolumeEmbeddingNormalizationPackage
    (H : ℕ) : Z2GaugeInvariantCrossVolumeEmbeddingNormalizationPackage H where
  scale := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H
  scale_eq := rfl
  scale_pos := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos H
  normalizedFormula :=
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback H
  rawFormula :=
    finiteEvenFourTorusZ2GaugeInvariantConfigurationCoarsePullback_eq_scale_inv_mul_embedding H

end

end MathlibAnalytic
end MGAP4D
