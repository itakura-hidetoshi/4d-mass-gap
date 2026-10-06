import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceLocalTilt
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-!
# Signed one-source-coordinate L2 localization

The actual kernel-weighted source row J(.,z)x is an element of the EXISTING
pair-Haar L2. Its pairing with the local source tilt only sees the conditional
projection keeping the single source-right coordinate y.right(e). This source
projection is NOT the posterior output projection P_e on joint L2.

Center the signed row by its actual integral O_x(z). The source response splits
exactly into its scalar mean term and a centered one-coordinate inner product.
Cauchy--Schwarz bounds the latter without first replacing x by |x|. The output
half-density drift is retained, with its scalar correction, in the ORIGINAL
defect and its resampling energy. The actual frozen family is unchanged.

A compact-row bound is used only for finite-volume L2 membership, not as a
uniform quantitative estimate. No spatial decay, independence, vanishing
source-coordinate projection, physicality or excited-sector claim is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStatePosteriorJoint

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "μP" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure H N hN beta hbeta
local notation "J" => jointTransferKernel H N hN beta hbeta
local notation "Obs" => jointTransferBCF H N hN beta hbeta
local notation "Out" => outputRightLinkTilt H N hN beta hbeta
local notation "Resp" => sourceLinkResponse H N hN beta hbeta
local notation "Rate" => (Real.exp (2 * beta) - 1)

local instance sourceCoordinatePairProbability : IsProbabilityMeasure μP := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The sigma-algebra keeping ONE source-right link, not all coordinates off a target. -/
def sourceCoordinateSigma (e : Link) : MeasurableSpace Joint :=
  MeasurableSpace.comap (fun y : Joint => y.2 e) inferInstance

theorem sourceCoordinateSigma_le (e : Link) :
    sourceCoordinateSigma H N e ≤ (inferInstance : MeasurableSpace Joint) := by
  exact measurable_iff_comap_le.mp ((measurable_pi_apply e).comp measurable_snd)

/-- Conditional projection on the existing pair-Haar source space. -/
def sourceCoordinateProjection (e : Link) (f : PairL2) : PairL2 :=
  (condExpL2 ℝ ℝ (sourceCoordinateSigma_le H N e) f : PairL2)

theorem sourceCoordinateProjection_norm_le (e : Link) (f : PairL2) :
    ‖sourceCoordinateProjection H N e f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le (sourceCoordinateSigma_le H N e) f

private theorem sourceKernelRow_continuous (z : Joint) : Continuous (fun y => J y z) := by
  change Continuous (fun y : Joint =>
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖ ^ 2)⁻¹ *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta (y, z) /
        continuousJointSqrtDensity H N hN beta hbeta z)
  exact (continuous_const.mul
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous H N beta).comp
      (continuous_id.prodMk continuous_const))).div_const _

/-- Finite-volume membership of the SIGNED row; no uniform row bound is claimed. -/
theorem sourceWeightedRow_memLp_two (x : PairL2) (z : Joint) :
    MemLp (fun y => J y z * x y) 2 μP := by
  let row : BoundedContinuousFunction Joint ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => J y z, sourceKernelRow_continuous H N hN beta hbeta z⟩
  apply (Lp.memLp x).of_le_mul (c := ‖row‖)
    ((sourceKernelRow_continuous H N hN beta hbeta z).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable x))
  filter_upwards with y
  change ‖J y z * x y‖ ≤ ‖row‖ * ‖x y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (row.norm_coe_le_norm y) (norm_nonneg _)

def sourceWeightedRowL2 (x : PairL2) (z : Joint) : PairL2 :=
  (sourceWeightedRow_memLp_two H N hN beta hbeta x z).toLp (fun y => J y z * x y)

theorem sourceWeightedRowL2_ae (x : PairL2) (z : Joint) :
    sourceWeightedRowL2 H N hN beta hbeta x z =ᵐ[μP] fun y => J y z * x y :=
  (sourceWeightedRow_memLp_two H N hN beta hbeta x z).coeFn_toLp

/-- Literal local tilt function before passing to L2. -/
def sourceTiltValue (e : Link) (z : Joint) (g : GaugeT) (y : Joint) : ℝ :=
  sourceRightLinkTilt N beta (y.2 e) (z.2 e) g - 1

private theorem sourceTiltScalar_continuous (a g : GaugeT) :
    Continuous (fun u : GaugeT => sourceRightLinkTilt N beta u a g - 1) := by
  unfold sourceRightLinkTilt
  exact (continuous_const.mul
    (((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp (continuous_inv.mul continuous_const)).sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy N).comp (continuous_inv.mul continuous_const)))).exp.sub continuous_const

/-- Measurability uses only the source-right coordinate at e. -/
theorem sourceTiltValue_source_measurable (e : Link) (z : Joint) (g : GaugeT) :
    @StronglyMeasurable Joint ℝ (sourceCoordinateSigma H N e) _
      (sourceTiltValue H N beta e z g) := by
  exact (sourceTiltScalar_continuous N beta (z.2 e) g).stronglyMeasurable.comp_measurable
    (measurable_iff_comap_le.mpr le_rfl)

private theorem sourceTiltValue_continuous (e : Link) (z : Joint) (g : GaugeT) :
    Continuous (sourceTiltValue H N beta e z g) :=
  (sourceTiltScalar_continuous N beta (z.2 e) g).comp
    ((continuous_apply e).comp continuous_snd)

theorem sourceTiltValue_memLp_two (e : Link) (z : Joint) (g : GaugeT) :
    MemLp (sourceTiltValue H N beta e z g) 2 μP := by
  apply MemLp.of_bound (sourceTiltValue_continuous H N beta e z g).aestronglyMeasurable Rate
  exact Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs] using
      sourceRightLinkTilt_sub_one_abs_le N hN beta hbeta (y.2 e) (z.2 e) g

def sourceTiltL2 (e : Link) (z : Joint) (g : GaugeT) : PairL2 :=
  (sourceTiltValue_memLp_two H N hN beta hbeta e z g).toLp (sourceTiltValue H N beta e z g)

theorem sourceTiltL2_ae (e : Link) (z : Joint) (g : GaugeT) :
    sourceTiltL2 H N hN beta hbeta e z g =ᵐ[μP] sourceTiltValue H N beta e z g :=
  (sourceTiltValue_memLp_two H N hN beta hbeta e z g).coeFn_toLp

theorem sourceTiltL2_source_measurable (e : Link) (z : Joint) (g : GaugeT) :
    AEStronglyMeasurable[sourceCoordinateSigma H N e]
      (fun y => sourceTiltL2 H N hN beta hbeta e z g y) μP :=
  (sourceTiltValue_source_measurable H N beta e z g).aestronglyMeasurable.congr
    (sourceTiltL2_ae H N hN beta hbeta e z g).symm

/-- No volume factor occurs in the local multiplier's L2 norm. -/
theorem sourceTiltL2_norm_le (e : Link) (z : Joint) (g : GaugeT) :
    ‖sourceTiltL2 H N hN beta hbeta e z g‖ ≤ Rate := by
  have hRate : 0 ≤ Rate := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hNorm : ‖sourceTiltL2 H N hN beta hbeta e z g‖ ^ 2 =
      ∫ y, sourceTiltValue H N beta e z g y ^ 2 ∂μP := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [sourceTiltL2_ae H N hN beta hbeta e z g] with y hy
    rw [hy]
    simp only [Real.norm_eq_abs, sq_abs]
  have hInt : (∫ y, sourceTiltValue H N beta e z g y ^ 2 ∂μP) ≤ Rate ^ 2 := by
    calc
      _ ≤ ∫ _y : Joint, Rate ^ 2 ∂μP := by
        apply integral_mono (sourceTiltValue_memLp_two H N hN beta hbeta e z g).integrable_sq
          (integrable_const _)
        intro y
        have h := pow_le_pow_left₀ (abs_nonneg _)
          (sourceRightLinkTilt_sub_one_abs_le N hN beta hbeta (y.2 e) (z.2 e) g) 2
        simpa only [sq_abs] using h
      _ = _ := by simp
  nlinarith [norm_nonneg (sourceTiltL2 H N hN beta hbeta e z g)]

/-- Exact orthogonal-projection identity on the source carrier. -/
theorem sourceCoordinateProjection_inner (e : Link) (f : PairL2) (z : Joint) (g : GaugeT) :
    inner ℝ (sourceCoordinateProjection H N e f) (sourceTiltL2 H N hN beta hbeta e z g) =
      inner ℝ f (sourceTiltL2 H N hN beta hbeta e z g) :=
  inner_condExpL2_eq_inner_fun (sourceCoordinateSigma_le H N e) f
    (sourceTiltL2 H N hN beta hbeta e z g)
    (sourceTiltL2_source_measurable H N hN beta hbeta e z g)

/-- The original signed source response is the row/tilt inner product. -/
theorem sourceLinkResponse_eq_row_inner (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Resp x e z g = inner ℝ (sourceWeightedRowL2 H N hN beta hbeta x z)
      (sourceTiltL2 H N hN beta hbeta e z g) := by
  rw [L2.inner_def]
  unfold sourceLinkResponse
  apply integral_congr_ae
  filter_upwards [sourceWeightedRowL2_ae H N hN beta hbeta x z,
    sourceTiltL2_ae H N hN beta hbeta e z g] with y hw ht
  rw [hw, ht]
  simp only [sourceTiltValue, RCLike.inner_apply, conj_trivial]
  ring

/-- Only the one-source-coordinate projection contributes; x remains signed. -/
theorem sourceLinkResponse_eq_coordinate_inner (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Resp x e z g = inner ℝ
      (sourceCoordinateProjection H N e (sourceWeightedRowL2 H N hN beta hbeta x z))
      (sourceTiltL2 H N hN beta hbeta e z g) := by
  rw [sourceCoordinateProjection_inner, sourceLinkResponse_eq_row_inner]

/-- Cauchy--Schwarz with the explicitly bounded one-link multiplier. -/
theorem sourceTilt_inner_abs_le (f : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |inner ℝ f (sourceTiltL2 H N hN beta hbeta e z g)| ≤ Rate * ‖f‖ := by
  calc
    _ ≤ ‖f‖ * ‖sourceTiltL2 H N hN beta hbeta e z g‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm f (sourceTiltL2 H N hN beta hbeta e z g)
    _ ≤ ‖f‖ * Rate :=
      mul_le_mul_of_nonneg_left (sourceTiltL2_norm_le H N hN beta hbeta e z g) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem sourceLinkResponse_abs_le_coordinateNorm (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |Resp x e z g| ≤ Rate *
      ‖sourceCoordinateProjection H N e (sourceWeightedRowL2 H N hN beta hbeta x z)‖ := by
  rw [sourceLinkResponse_eq_coordinate_inner]
  exact sourceTilt_inner_abs_le H N hN beta hbeta _ e z g

/-- Constant in the same pair-Haar L2, not a new carrier. -/
def sourceConstantL2 (a : ℝ) : PairL2 :=
  (MemLp.of_bound aestronglyMeasurable_const ‖a‖ (Eventually.of_forall fun _ : Joint => le_rfl)).toLp
    (fun _ : Joint => a)

private theorem sourceConstantL2_ae (a : ℝ) :
    sourceConstantL2 H N a =ᵐ[μP] fun _ : Joint => a :=
  (MemLp.of_bound aestronglyMeasurable_const ‖a‖
    (Eventually.of_forall fun _ : Joint => le_rfl) : MemLp (fun _ : Joint => a) 2 μP).coeFn_toLp

def sourceTiltMean (e : Link) (z : Joint) (g : GaugeT) : ℝ :=
  ∫ y, sourceTiltValue H N beta e z g y ∂μP

private theorem sourceConstantL2_inner_tilt (a : ℝ) (e : Link) (z : Joint) (g : GaugeT) :
    inner ℝ (sourceConstantL2 H N a) (sourceTiltL2 H N hN beta hbeta e z g) =
      a * sourceTiltMean H N beta e z g := by
  rw [L2.inner_def, sourceTiltMean, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sourceConstantL2_ae H N a, sourceTiltL2_ae H N hN beta hbeta e z g] with y hc ht
  rw [hc, ht]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Center the actual signed weighted row by its actual integral before keeping e. -/
def sourceCenteredCoordinate (x : PairL2) (e : Link) (z : Joint) : PairL2 :=
  sourceCoordinateProjection H N e
    (sourceWeightedRowL2 H N hN beta hbeta x z - sourceConstantL2 H N (Obs x z))

theorem sourceCenteredCoordinate_norm_le (x : PairL2) (e : Link) (z : Joint) :
    ‖sourceCenteredCoordinate H N hN beta hbeta x e z‖ ≤
      ‖sourceWeightedRowL2 H N hN beta hbeta x z - sourceConstantL2 H N (Obs x z)‖ :=
  sourceCoordinateProjection_norm_le H N e _

/-- Centering really gives zero source mean, not a formal subtraction only. -/
theorem sourceCenteredCoordinate_integral_zero (x : PairL2) (e : Link) (z : Joint) :
    (∫ y, sourceCenteredCoordinate H N hN beta hbeta x e z y ∂μP) = 0 := by
  let w := sourceWeightedRowL2 H N hN beta hbeta x z
  let a := sourceConstantL2 H N (Obs x z)
  have hStationary : (∫ y, sourceCoordinateProjection H N e (w - a) y ∂μP) =
      ∫ y, (w - a) y ∂μP := by
    simpa only [Measure.restrict_univ] using
      (integral_condExpL2_eq_of_fin_meas_real (𝕜 := ℝ) (hm := sourceCoordinateSigma_le H N e)
        (w - a) (s := Set.univ) MeasurableSet.univ (measure_ne_top _ _))
  change (∫ y, sourceCoordinateProjection H N e (w - a) y ∂μP) = 0
  rw [hStationary]
  calc
    _ = ∫ y, J y z * x y - Obs x z ∂μP := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub w a, sourceWeightedRowL2_ae H N hN beta hbeta x z,
        sourceConstantL2_ae H N (Obs x z)] with y hs hw ha
      exact hs.trans (by change w y - a y = _; rw [hw, ha])
    _ = 0 := by
      rw [integral_sub (jointTransferKernel_integrable H N hN beta hbeta x z) (integrable_const _),
        ← jointTransferBCF_eq_integral_kernel]
      simp

/-- Separate the scalar mean from the genuinely centered source-coordinate pairing. -/
theorem sourceLinkResponse_eq_centeredCoordinate (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    Resp x e z g = Obs x z * sourceTiltMean H N beta e z g +
      inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
        (sourceTiltL2 H N hN beta hbeta e z g) := by
  rw [sourceCenteredCoordinate, sourceCoordinateProjection_inner, inner_sub_left,
    sourceConstantL2_inner_tilt, ← sourceLinkResponse_eq_row_inner]
  ring

/-- The original defect retains the corrected output drift. -/
theorem jointTransferLinkDifference_eq_centeredCoordinate (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    jointTransferLinkDifference H N hN beta hbeta x e z g =
      (1 - Out z e g * (1 + sourceTiltMean H N beta e z g)) * Obs x z -
        Out z e g * inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
          (sourceTiltL2 H N hN beta hbeta e z g) := by
  rw [jointTransferLinkDifference_eq_sourceTilt, sourceLinkResponse_eq_centeredCoordinate]
  ring

/-- A constructed signed-coordinate bound. The scalar output drift is NOT dropped. -/
theorem jointTransferLinkDifference_abs_le_centeredCoordinate (x : PairL2) (e : Link) (z : Joint) (g : GaugeT) :
    |jointTransferLinkDifference H N hN beta hbeta x e z g| ≤
      |1 - Out z e g * (1 + sourceTiltMean H N beta e z g)| * |Obs x z| +
        Out z e g * Rate * ‖sourceCenteredCoordinate H N hN beta hbeta x e z‖ := by
  rw [jointTransferLinkDifference_eq_centeredCoordinate]
  calc
    _ ≤ |(1 - Out z e g * (1 + sourceTiltMean H N beta e z g)) * Obs x z| +
        |Out z e g * inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
          (sourceTiltL2 H N hN beta hbeta e z g)| := abs_sub_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos (outputRightLinkTilt_pos H N hN beta hbeta z e g)]
      have h := mul_le_mul_of_nonneg_left
        (sourceTilt_inner_abs_le H N hN beta hbeta
          (sourceCenteredCoordinate H N hN beta hbeta x e z) e z g)
        (outputRightLinkTilt_pos H N hN beta hbeta z e g).le
      nlinarith

/-- Exact substitution into the original signed resampling energy. -/
theorem jointTransferLinkResamplingEnergy_eq_centeredCoordinate (x : PairL2) (e : Link) :
    jointTransferLinkResamplingEnergy H N hN beta hbeta x e =
      ∫ z, ∫ g, ((1 - Out z e g * (1 + sourceTiltMean H N beta e z g)) * Obs x z -
        Out z e g * inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
          (sourceTiltL2 H N hN beta hbeta e z g)) ^ 2 ∂Nu z.1 z.2 e ∂μJ := by
  unfold jointTransferLinkResamplingEnergy
  simp only [jointTransferLinkDifference_eq_centeredCoordinate]

/-- The combined square has a genuine outer integral under the old joint law. -/
theorem centeredCoordinateDefect_sq_joint_integrable (x : PairL2) (e : Link) :
    Integrable (fun z => ∫ g,
      ((1 - Out z e g * (1 + sourceTiltMean H N beta e z g)) * Obs x z -
        Out z e g * inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
          (sourceTiltL2 H N hN beta hbeta e z g)) ^ 2 ∂Nu z.1 z.2 e) μJ := by
  simpa only [jointTransferLinkDifference_eq_centeredCoordinate] using
    jointTransferLinkResamplingSquare_integrable H N hN beta hbeta x e

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)
local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Nu" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure Hn 2 Pos (beta n) (hbeta n)
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenVec" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "Obs" => jointTransferBCF Hn 2 Pos (beta n) (hbeta n)
local notation "Out" => outputRightLinkTilt Hn 2 Pos (beta n) (hbeta n)
local notation "Avg" => sourceTiltMean Hn 2 (beta n)
local notation "Center" => sourceCenteredCoordinate Hn 2 Pos (beta n) (hbeta n)
local notation "Tilt" => sourceTiltL2 Hn 2 Pos (beta n) (hbeta n)

/-- The unchanged actual frozen family, including r=0 and the two distinct couplings. -/
theorem fineFrozenInitialEnergy_eq_centeredCoordinate :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n) FrozenVec =
      (1 / 12 : ℝ) * ∑ e : Link, ∫ z, ∫ g,
        ((1 - Out z e g * (1 + Avg e z g)) * Obs Orbit z -
          Out z e g * inner ℝ (Center Orbit e z) (Tilt e z g)) ^ 2 ∂Nu z.1 z.2 e ∂μJ := by
  rw [fineFrozenInitialEnergy_eq_resampling]
  simp_rw [jointTransferLinkResamplingEnergy_eq_centeredCoordinate]

end FrozenFamily

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic
