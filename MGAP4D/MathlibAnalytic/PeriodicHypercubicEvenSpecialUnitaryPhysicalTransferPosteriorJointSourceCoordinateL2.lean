import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateProjection

/-!
# Centered source-coordinate response and the original frozen energy

The actual signed source row is centered by its original integral. Its
one-coordinate projection isolates the signed response while retaining the
corrected output drift. Neither the posterior law nor the frozen vector is
replaced. The compact-row membership proof in the projection module is not a
volume-uniform estimate. P3 distance decay remains a quantitative obligation.
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

local instance sourceCenteredPairProbability : IsProbabilityMeasure μP := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

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
  rw [sourceRealScalar_inner_eq_mul]

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
  letI : IsProbabilityMeasure μP := sourceCenteredPairProbability H N
  let w := sourceWeightedRowL2 H N hN beta hbeta x z
  let a := sourceConstantL2 H N (Obs x z)
  have hStationary : (∫ y, sourceCoordinateProjection H N e (w - a) y ∂μP) =
      ∫ y, (w - a) y ∂μP := by
    simpa only [Measure.restrict_univ] using
      (integral_condExpL2_eq_of_fin_meas_real (𝕜 := ℝ) (μ := μP) (hm := sourceCoordinateSigma_le H N e)
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
          (sourceTiltL2 H N hN beta hbeta e z g)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos (outputRightLinkTilt_pos H N hN beta hbeta z e g)]
      have h := mul_le_mul_of_nonneg_left
        (sourceTilt_inner_abs_le H N hN beta hbeta
          (sourceCenteredCoordinate H N hN beta hbeta x e z) e z g)
        (outputRightLinkTilt_pos H N hN beta hbeta z e g).le
      nlinarith

/-- The combined square is integrable at every original posterior fiber. -/
theorem centeredCoordinateDefect_sq_posterior_integrable (x : PairL2) (e : Link) (z : Joint) :
    Integrable (fun g =>
      ((1 - Out z e g * (1 + sourceTiltMean H N beta e z g)) * Obs x z -
        Out z e g * inner ℝ (sourceCenteredCoordinate H N hN beta hbeta x e z)
          (sourceTiltL2 H N hN beta hbeta e z g)) ^ 2) (Nu z.1 z.2 e) := by
  simpa only [jointTransferLinkDifference_eq_centeredCoordinate] using
    jointTransferLinkDifference_sq_posterior_integrable H N hN beta hbeta x e z

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
