import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointLeftQuotientMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarL2Equiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedBlockTransferRestriction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation

/-!
# Exact BCF representatives of normalized physical pair-transfer outputs

The literal continuous pair Wilson kernel regularizes an arbitrary pair-Haar
L2 input. Dominated convergence proves continuity of its integral output;
the existing Hilbert-Schmidt integral theorem identifies its L2 class.

The already-constructed continuous positive vacuum gives a continuous positive
representative of the ORIGINAL joint density. Division by its square root is
continuous on the compact finite-volume configuration space. The resulting BCF
represents the EXISTING half-density image of the actual physical transfer.
No regularity is inferred from a.e. equality, and no new measure is substituted.

This is qualitative finite-volume regularization. No volume-uniform inverse
density bound, small oscillation, support-distance tail, or identification of
physical transfer with posterior conditional expectation is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

local instance exactBCFPairProbability (H N : ℕ) :
    IsProbabilityMeasure (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance exactBCFJointProbability (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "KP" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta
local notation "RawTransfer" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "lambda" => ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖
local notation "OmegaC" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative H N hN beta hbeta
local notation "UJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta

include hN hbeta

/-- The source is integrated first, exactly as in the existing kernel pairing. -/
def pairTransferIntegral (f : PairL2) (z : Joint) : ℝ := ∫ x, KP (x, z) * f x ∂μP

private theorem pairTransferIntegrand_norm_le (f : PairL2) (x z : Joint) :
    ‖KP (x, z) * f x‖ ≤ ‖f x‖ := by
  rw [norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
      H N hN beta hbeta (x, z)) (norm_nonneg (f x))

/-- Every fiber integral exists, not only for almost every output point. -/
theorem pairTransferIntegrand_integrable (f : PairL2) (z : Joint) :
    Integrable (fun x => KP (x, z) * f x) μP := by
  have hf : Integrable (fun x => f x) μP :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hk := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous H N beta
  apply hf.norm.mono'
    ((hk.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => pairTransferIntegrand_norm_le H N hN beta hbeta f x z)

/-- Continuity is proved by domination by the L1 norm of the original L2 input. -/
theorem pairTransferIntegral_continuous (f : PairL2) :
    Continuous (pairTransferIntegral H N beta f) := by
  have hf : Integrable (fun x => f x) μP :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hk := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous H N beta
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · intro z
    exact (pairTransferIntegrand_integrable H N hN beta hbeta f z).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall (fun x => pairTransferIntegrand_norm_le H N hN beta hbeta f x z)
  · exact hf.norm
  · exact Eventually.of_forall (fun x =>
      (hk.comp (continuous_const.prodMk continuous_id)).mul continuous_const)

/-- Explicit raw output bound; normalization and inverse density are not hidden in it. -/
theorem pairTransferIntegral_norm_le_integral_norm (f : PairL2) (z : Joint) :
    ‖pairTransferIntegral H N beta f z‖ ≤ ∫ x, ‖f x‖ ∂μP := by
  have hf : Integrable (fun x => f x) μP :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  exact norm_integral_le_of_norm_le hf.norm
    (Eventually.of_forall (fun x => pairTransferIntegrand_norm_le H N hN beta hbeta f x z))

/-- BCF of the actual normalized physical pair-transfer output. -/
def pairTransferBCF (f : PairL2) : BoundedContinuousFunction Joint ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => (lambda ^ 2)⁻¹ * pairTransferIntegral H N beta f z,
      continuous_const.mul (pairTransferIntegral_continuous H N hN beta hbeta f)⟩

/-- The existing raw operator has the literal integral as its a.e. representative. -/
theorem pairTransferIntegral_ae_eq (f : PairL2) :
    RawTransfer f =ᵐ[μP] pairTransferIntegral H N beta f := by
  let k : Joint → Joint → ℝ := fun x z => KP (x, z)
  have hkMeas := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_aestronglyMeasurable H N beta
  have hkBound : ∀ x z, |k x z| ≤ 1 := fun x z =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one H N hN beta hbeta (x, z)
  have hEq := realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2 (μ := μP) k
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2 H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernelL2_coeFn H N hN beta hbeta)
    hkMeas hkBound f
  change realL2HilbertSchmidtKernelOperator _ f =ᵐ[μP] _
  rw [hEq]
  exact realL2BoundedKernelIntegralOutputL2_coeFn k hkMeas hkBound f

/-- Normalization is the original physical transfer normalization. -/
theorem pairTransferBCF_ae_eq (f : PairL2) :
    NormTransfer f =ᵐ[μP] pairTransferBCF H N hN beta hbeta f := by
  change ((lambda ^ 2)⁻¹ • RawTransfer f) =ᵐ[μP] _
  filter_upwards [Lp.coeFn_smul ((lambda ^ 2)⁻¹) (RawTransfer f),
    pairTransferIntegral_ae_eq H N hN beta hbeta f] with z hz hraw
  rw [hz]
  change (lambda ^ 2)⁻¹ * (RawTransfer f) z = _
  rw [hraw]
  rfl

/-- The concrete BCF represents exactly the old pair-Haar L2 vector. -/
theorem pairTransferBCF_rep_eq (f : PairL2) :
    BoundedContinuousFunction.toLp 2 μP ℝ (pairTransferBCF H N hN beta hbeta f) =
      NormTransfer f := by
  apply Lp.ext
  exact (BoundedContinuousFunction.coeFn_toLp 2 μP ℝ _).trans
    (pairTransferBCF_ae_eq H N hN beta hbeta f).symm

/-- Continuous representative of the already-existing normalized joint weight. -/
def continuousJointWeight (z : Joint) : ℝ :=
  lambda⁻¹ * (OmegaC z.1 *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta z.1 z.2 * OmegaC z.2)

theorem continuousJointWeight_continuous :
    Continuous (continuousJointWeight H N hN beta hbeta) := by
  have hO := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous H N hN beta hbeta
  have hK := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta
  exact continuous_const.mul (((hO.comp continuous_fst).mul hK).mul (hO.comp continuous_snd))

/-- Pointwise positivity is proved before division; no uniform-in-volume floor is used. -/
theorem continuousJointWeight_pos (z : Joint) :
    0 < continuousJointWeight H N hN beta hbeta z := by
  exact mul_pos
    (inv_pos.mpr (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H N hN beta hbeta))
    (mul_pos
      (mul_pos
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos H N hN beta hbeta z.1)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta z.1 z.2))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos H N hN beta hbeta z.2))

/-- The new continuous function is not a new law: it equals the existing density a.e. -/
theorem continuousJointWeight_ae_eq :
    continuousJointWeight H N hN beta hbeta =ᵐ[μP]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight H N hN beta hbeta := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hO := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing H N hN beta hbeta
  have hf := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hO
  have hs := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hO
  change _ =ᵐ[μ.prod μ] _
  filter_upwards [hf, hs] with z h1 h2
  unfold continuousJointWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  rw [h1, h2]

/-- Positive continuous half-density representative of the original joint law. -/
def continuousJointSqrtDensity (z : Joint) : ℝ :=
  Real.sqrt (continuousJointWeight H N hN beta hbeta z)

theorem continuousJointSqrtDensity_continuous :
    Continuous (continuousJointSqrtDensity H N hN beta hbeta) :=
  Real.continuous_sqrt.comp (continuousJointWeight_continuous H N hN beta hbeta)

theorem continuousJointSqrtDensity_pos (z : Joint) :
    0 < continuousJointSqrtDensity H N hN beta hbeta z :=
  Real.sqrt_pos.mpr (continuousJointWeight_pos H N hN beta hbeta z)

/-- Correct pair-Haar a.e. identification of the half-density. -/
theorem continuousJointSqrtDensity_ae_eq :
    continuousJointSqrtDensity H N hN beta hbeta =ᵐ[μP]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity H N hN beta hbeta :=
  (continuousJointWeight_ae_eq H N hN beta hbeta).mono (fun _ h => congrArg Real.sqrt h)

/-- Construct a genuine joint BCF by dividing the regularized output by the
continuous positive half-density. No L2 representative is evaluated at a point. -/
def jointTransferBCF (f : PairL2) : BoundedContinuousFunction Joint ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun z => pairTransferBCF H N hN beta hbeta f z / continuousJointSqrtDensity H N hN beta hbeta z,
      (pairTransferBCF H N hN beta hbeta f).continuous.div
        (continuousJointSqrtDensity_continuous H N hN beta hbeta)
        (fun z => (continuousJointSqrtDensity_pos H N hN beta hbeta z).ne')⟩

/-- Exact identification on the original joint law with the existing half-density map. -/
theorem jointTransferBCF_rep_eq (f : PairL2) :
    BCFRep (jointTransferBCF H N hN beta hbeta f) = UJoint (NormTransfer f) := by
  have hAC := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar H N hN beta hbeta
  have hpair := hAC.ae_eq (pairTransferBCF_ae_eq H N hN beta hbeta f)
  have hdensity := hAC.ae_eq (continuousJointSqrtDensity_ae_eq H N hN beta hbeta)
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μJ ℝ (jointTransferBCF H N hN beta hbeta f),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2_coeFn
      H N hN beta hbeta (NormTransfer f), hpair, hdensity] with z hbcf hu hp hd
  change (BoundedContinuousFunction.toLp 2 μJ ℝ (jointTransferBCF H N hN beta hbeta f)) z =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarToGroundStateJointL2 H N hN beta hbeta (NormTransfer f) z
  rw [hbcf, hu]
  change pairTransferBCF H N hN beta hbeta f z / continuousJointSqrtDensity H N hN beta hbeta z =
    (NormTransfer f) z / periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity H N hN beta hbeta z
  rw [hp, hd]

/-- No loss constant appears in the L2 norm of the constructed representative. -/
theorem jointTransferBCF_rep_norm (f : PairL2) :
    ‖BCFRep (jointTransferBCF H N hN beta hbeta f)‖ = ‖NormTransfer f‖ := by
  rw [jointTransferBCF_rep_eq]
  exact (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
    H N hN beta hbeta).norm_map _

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
