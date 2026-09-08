import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferStrictlyPositiveTopEigenvector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarContinuousVacuum_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Pointwise synthesis of a fixed vector in the canonical one-slab
Moore--Aronszajn feature Hilbert space.  This is deliberately defined before
specializing to the physical vacuum, so the quotient-to-continuous bridge is
visible independently of the eigenvector equation. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  inner ℝ v
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta).feature B)

/-- Feature synthesis is continuous because the canonical kernel feature is
continuous and the first inner-product argument is fixed. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v) := by
  exact continuous_const.inner
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_continuous
      H N hN beta hbeta)

/-- The pointwise synthesis is uniformly bounded by the norm of its fixed
feature-space vector. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v B‖ ≤ ‖v‖ := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  calc
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v B‖ = ‖inner ℝ v (C.feature B)‖ := by rfl
    _ ≤ ‖v‖ * ‖C.feature B‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_norm_le_one
          H N hN beta hbeta B)
        (norm_nonneg v)
    _ = ‖v‖ := mul_one _

/-- Every continuous feature synthesis is a genuine Haar-`L²` function. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let s := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
    H N hN beta hbeta v
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hmeas : AEStronglyMeasurable s μ :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_continuous
      H N hN beta hbeta v).aestronglyMeasurable
  have htop : MemLp s ∞ μ :=
    memLp_top_of_bound hmeas ‖v‖ <| by
      filter_upwards with B
      exact
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_norm_le
          H N hN beta hbeta v B
  exact htop.mono_exponent (by norm_num)

/-- Canonical Haar-`L²` class represented by feature synthesis. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_memLp_two
    H N hN beta hbeta v).toLp
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v)

/-- The synthesis `L²` class has the literal continuous synthesis function as
an almost-everywhere representative. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
        H N hN beta hbeta v =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v := by
  exact MemLp.coeFn_toLp
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_memLp_two
      H N hN beta hbeta v)

/-- Exact synthesis/adjoint identity.  Pointwise continuous synthesis of `v`
represents precisely the Hilbert adjoint `A† v` of the complete Haar-`L²`
feature analysis operator. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_eq_adjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
        H N hN beta hbeta).FeatureHilbert) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
        H N hN beta hbeta v =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
        H N hN beta hbeta)†) v := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta
  let A := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
    H N hN beta hbeta v
  apply ext_inner_right ℝ
  intro f
  have hfInt : Integrable (fun B => f B • C.feature B) μ := by
    simpa [μ, C] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature_weighted_integrable
        H N hN beta hbeta f
  calc
    inner ℝ S f =
        ∫ B, inner ℝ v (f B • C.feature B) ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_coeFn
          H N hN beta hbeta v] with B hB
      rw [hB]
      rw [realL2Scalar_inner_eq_mul]
      rw [real_inner_smul_right]
      rfl
    _ = inner ℝ v (∫ B, f B • C.feature B ∂μ) := by
      exact integral_inner hfInt v
    _ = inner ℝ v (A f) := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator_apply]
    _ = inner ℝ ((A†) v) f := by
      exact (ContinuousLinearMap.adjoint_inner_left A f v).symm
    _ = inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureAnalysisOperator
          H N hN beta hbeta)†) v) f := by
      rfl

/-- Unscaled continuous synthesis attached to the canonical nonnegative
physical top eigenvector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta)) B

/-- The unscaled physical synthesis is continuous. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
        H N hN beta hbeta) := by
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_continuous
      H N hN beta hbeta _

/-- The `L²` class of unscaled physical synthesis is the ambient transfer
output on the existing physical vacuum class. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisL2_eq_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta)) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_eq_adjoint]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator_apply]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_eq_adjoint_comp_analysis]
  rfl

/-- The unscaled physical synthesis class is exactly `λ Ω` in ambient Haar
`L²`, with `λ = ‖T_phys‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisL2_eq_topNorm_smul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta hbeta)) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisL2_eq_transfer]
  have heigenP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H N hN beta hbeta
  have hval := congrArg Subtype.val heigenP
  simpa using hval

/-- Canonical continuous representative of the physical Wilson vacuum.

It is defined by feature synthesis rather than by selecting pointwise values of
the pre-existing `L²` quotient representative:

`Ω_c(B) = ‖T_phys‖⁻¹ ⟪A_phys Ω, Φ(B)⟫`.

The positive top-transfer norm makes the normalization canonical. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction
      H N hN beta hbeta B

/-- The canonical physical vacuum representative is continuous on the full
spatial boundary configuration space. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta) := by
  exact continuous_const.mul
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisFunction_continuous
      H N hN beta hbeta)

/-- The canonical continuous vacuum representative belongs to Haar `L²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta)
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let omegaC :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  have hmeas : AEStronglyMeasurable omegaC μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).aestronglyMeasurable
  have htop : MemLp omegaC ∞ μ :=
    memLp_top_of_bound hmeas (‖lambda⁻¹‖ * ‖v‖) <| by
      filter_upwards with B
      change ‖lambda⁻¹ *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
          H N hN beta hbeta v B‖ ≤ ‖lambda⁻¹‖ * ‖v‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction_norm_le
          H N hN beta hbeta v B)
        (norm_nonneg lambda⁻¹)
  exact htop.mono_exponent (by norm_num)

/-- Haar-`L²` class induced by the canonical continuous vacuum representative. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
    H N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta)

/-- The induced `L²` class is inverse-top-norm times the unscaled synthesis
class. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2_eq_inv_smul_synthesis
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2
        H N hN beta hbeta =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ •
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta)) := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta)
  let S := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2
    H N hN beta hbeta v
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
        H N hN beta hbeta),
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisL2_coeFn
      H N hN beta hbeta v,
    Lp.coeFn_smul lambda⁻¹ S] with B hC hS hsmul
  change
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
      H N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta)) B = (lambda⁻¹ • S) B
  rw [hC]
  change lambda⁻¹ *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabFeatureSynthesisFunction
        H N hN beta hbeta v B = (lambda⁻¹ • S) B
  rw [← hS]
  simpa only [Pi.smul_apply, smul_eq_mul] using hsmul.symm

/-- The continuous representative induces exactly the original canonical
nonnegative physical vacuum class.  No representative of the old quotient is
used in the construction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2
        H N hN beta hbeta =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  let lambda := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  let Omega :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H N hN beta hbeta :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2_eq_inv_smul_synthesis]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumSynthesisL2_eq_topNorm_smul]
  have hlambda : 0 < lambda := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
        H N hN beta hbeta
  change lambda⁻¹ • (lambda • Omega) = Omega
  rw [smul_smul]
  simp [hlambda.ne']

/-- The canonical continuous function is an almost-everywhere representative
of the already constructed physical vacuum `L²` class. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun B =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 B := by
  have hrep := MemLp.coeFn_toLp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_memLp_two
      H N hN beta hbeta)
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2
        H N hN beta hbeta =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta at hrep
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentativeL2_eq_existing]
    at hrep
  exact hrep.symm

end

end MathlibAnalytic
end MGAP4D