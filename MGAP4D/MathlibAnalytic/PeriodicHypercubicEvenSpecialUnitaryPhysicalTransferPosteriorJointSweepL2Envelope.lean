import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepUnionBound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentRightVariation

/-!
# Full posterior sweep bounds without sup norms or response-data assumptions

The projection union bound transfers #5220's genuinely constructed one-link
L2 envelope to every prefix and to the actual six-color stage energy. All
six color sweeps start from the SAME original vector. Reindex the existing
color fibers exactly; do not concatenate the colors or assume commutativity.

On arbitrary genuine joint L2, Profile(f) <= 4 InitialEnergy(f), where
InitialEnergy=(1/6) sum_e ||f-P_e f||^2 is continuous. The actual normalized
kernel output therefore satisfies

  Profile(O_x) <= (2/3) card(Link) (exp(16 beta)-1)^2 ||S |x|||^2.

The count is EXPLICIT: this is not volume-uniform or support-distance decay.
The point is to retain the L2 norm of the actual positive envelope instead
of its sup norm, with no ResponseData or small-coupling cutoff in this route.
Absolute input is not assumed to preserve the non-top sector. No q0 excitation
estimate, adjacent physical projection, or transfer/reconstruction commutation
is inserted. All existing no-go boundaries remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
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
local notation "Color" => PeriodicHypercubicEvenGroundStateSpatialColor
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "PairL2" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "PJoint" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "Profile" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy H N hN beta hbeta
local notation "ColorLoss" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss H N hN beta hbeta
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "Rate" => kernelRightVariationRate beta

/-- Initial one-link defects, all at the same original vector, normalized by 1/6. -/
def sixColorInitialResidualEnergy (f : JL2) : ℝ :=
  (1 / 6 : ℝ) * ∑ e : Link, ‖f - PJoint e f‖ ^ 2

theorem sixColorInitialResidualEnergy_nonneg (f : JL2) :
    0 ≤ sixColorInitialResidualEnergy H N hN beta hbeta f :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Continuity is proved on the original Hilbert topology, not assumed for oscillations. -/
theorem sixColorInitialResidualEnergy_continuous :
    Continuous (sixColorInitialResidualEnergy H N hN beta hbeta) := by
  unfold sixColorInitialResidualEnergy
  fun_prop

/-- Exact color-fiber reindexing for arbitrary link weights. -/
theorem posteriorLink_sum_eq_colorFiber_sum (a : Link → ℝ) :
    (∑ e : Link, a e) = ∑ c : Color, ∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H c, a e.1 := by
  calc
    _ = ∑ z : (Σ c : Color, PeriodicHypercubicEvenFixedSpatialColorLink H c), a z.2.1 := by
      refine Fintype.sum_equiv (periodicHypercubicEvenSpatialSliceLinkEquivSigmaFixedSpatialColor H) _ _ ?_
      intro e
      rfl
    _ = _ := Fintype.sum_sigma' (fun c : Color =>
      fun e : PeriodicHypercubicEvenFixedSpatialColorLink H c => a e.1)

/-- The canonical same-color path needs no same-color commutativity. -/
theorem fixedColorPathLoss_le_four_initial (c : Color) (f : JL2) :
    ColorLoss c f ≤ 4 * ∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H c, ‖f - PJoint e.1 f‖ ^ 2 := by
  let Pc := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
    H N hN beta hbeta c
  change realHilbertProjectionSweepPathLoss Pc
    ((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H c)).toList) f ≤ _
  simpa using realHilbertProjectionSweep_pathLoss_le_four_initial Pc
    (fun e => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
      H N hN beta hbeta e.1)
    (fun e x y => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
      H N hN beta hbeta e.1 x y)
    ((Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H c)).toList) f

/-- The actual normalized stage profile is controlled by initial L2 defects with constant four. -/
theorem sixColorProfileEnergy_le_four_initialResidualEnergy (f : JL2) :
    Profile f ≤ 4 * sixColorInitialResidualEnergy H N hN beta hbeta f := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_sq_sum_eq_colorPathLossSum]
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ c : Color,
        (4 * ∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H c, ‖f - PJoint e.1 f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun c _ => fixedColorPathLoss_le_four_initial H N hN beta hbeta c f)
        (by norm_num)
    _ = 4 * sixColorInitialResidualEnergy H N hN beta hbeta f := by
      rw [← Finset.mul_sum, ← posteriorLink_sum_eq_colorFiber_sum H (fun e => ‖f - PJoint e f‖ ^ 2)]
      unfold sixColorInitialResidualEnergy
      ring

/-- Combine the new bound with the existing intrinsic left-centered norm bound. -/
theorem sixColorProfileEnergy_le_min_centered_initial (f : JL2) :
    Profile f ≤ min (‖posteriorLeftCenteredOperator H N hN beta hbeta f‖ ^ 2)
      (4 * sixColorInitialResidualEnergy H N hN beta hbeta f) :=
  le_min (sixColorProfileEnergy_le_leftCenteredNormSq H N hN beta hbeta f)
    (sixColorProfileEnergy_le_four_initialResidualEnergy H N hN beta hbeta f)

/-- Align the already-proved literal energy with the standard BCF embedding at every prefix. -/
theorem posteriorStageEnergy_eq_bcfResidualNormSq (pre : List Link) (e : Link)
    (F : BoundedContinuousFunction Joint ℝ) :
    posteriorStageResidualEnergy H N hN beta hbeta pre e F =
      ‖realHilbertProjectionSweep PJoint pre (BCFRep F) -
        PJoint e (realHilbertProjectionSweep PJoint pre (BCFRep F))‖ ^ 2 := by
  rw [posteriorStageResidualEnergy_eq_projectionResidualNormSq
    H N hN beta hbeta pre e F F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm]
  simp only [posteriorScheduleL2_eq_projectionSchedule,
    jointBCF_boundedConcreteL2_eq_standardRepresentative]

/-- Reuse the CONSTRUCTED #5220 one-link envelope, rather than a final residual premise. -/
theorem jointTransferInitialResidual_sq_le_l2Envelope (x : PairL2) (e : Link) :
    ‖BCFRep (jointTransferBCF H N hN beta hbeta x) -
      PJoint e (BCFRep (jointTransferBCF H N hN beta hbeta x))‖ ^ 2 ≤
      Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2 := by
  have h := jointTransferPosteriorResidualEnergy_le H N hN beta hbeta x e
  rw [posteriorStageEnergy_eq_bcfResidualNormSq] at h
  simpa only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] using h

/-- An arbitrary chronological prefix is now controlled using only the actual L2 envelope. -/
theorem jointTransferStageEnergy_le_l2Envelope (x : PairL2) (pre : List Link) (e : Link) :
    posteriorStageResidualEnergy H N hN beta hbeta pre e (jointTransferBCF H N hN beta hbeta x) ≤
      4 * ((pre.length : ℝ) + 1) * (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  let f := BCFRep (jointTransferBCF H N hN beta hbeta x)
  let b := Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2
  have hList : ∀ cs : List Link, (cs.map fun t => ‖f - PJoint t f‖ ^ 2).sum ≤ (cs.length : ℝ) * b := by
    intro cs
    induction cs with
    | nil => simp
    | cons t cs ih =>
        have ht := jointTransferInitialResidual_sq_le_l2Envelope H N hN beta hbeta x t
        change ‖f - PJoint t f‖ ^ 2 ≤ b at ht
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
  rw [posteriorStageEnergy_eq_bcfResidualNormSq]
  have hStage := realHilbertProjectionSweep_stageResidual_sq_le_four_initial PJoint
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent H N hN beta hbeta)
    (fun t u v => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
      H N hN beta hbeta t u v) pre e f
  have h := hStage.trans (mul_le_mul_of_nonneg_left (hList (pre ++ [e])) (by norm_num : (0 : ℝ) ≤ 4))
  simpa only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one, mul_assoc] using h

/-- Full six-color bound: L2 rather than sup norm, and no ResponseData or cutoff.
The actual link count is retained explicitly and is not asserted to be uniform. -/
theorem jointTransferProfileEnergy_le_l2Envelope (x : PairL2) :
    Profile (BCFRep (jointTransferBCF H N hN beta hbeta x)) ≤
      (2 / 3 : ℝ) * (Fintype.card Link : ℝ) *
        (Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) := by
  let f := BCFRep (jointTransferBCF H N hN beta hbeta x)
  have hSum : (∑ e : Link, ‖f - PJoint e f‖ ^ 2) ≤
      ∑ _e : Link, Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2 :=
    Finset.sum_le_sum fun e _ => jointTransferInitialResidual_sq_le_l2Envelope H N hN beta hbeta x e
  calc
    _ ≤ 4 * sixColorInitialResidualEnergy H N hN beta hbeta f :=
      sixColorProfileEnergy_le_four_initialResidualEnergy H N hN beta hbeta f
    _ ≤ 4 * ((1 / 6 : ℝ) * ∑ _e : Link, Rate ^ 2 * ‖NormTransfer (pairAbsoluteInput H N x)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSum (by norm_num)) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end GeneralCarrier

section FrozenFamily

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenVec" => physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "FrozenEnergy" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "NormTransfer" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
  Hn 2 Pos (beta n) (hbeta n)

/-- Apply the cutoff-free L2 bound to the EXISTING frozen vector at its exact two couplings. -/
theorem fineFrozenProfileEnergy_le_l2Envelope :
    FrozenEnergy ≤ (2 / 3 : ℝ) * (Fintype.card Link : ℝ) *
      ((kernelRightVariationRate (beta n)) ^ 2 * ‖NormTransfer (pairAbsoluteInput Hn 2 Orbit)‖ ^ 2) := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  exact jointTransferProfileEnergy_le_l2Envelope Hn 2 Pos (beta n) (hbeta n) Orbit

/-- The beta_n=0 endpoint no longer requires a response matrix to be supplied. -/
theorem fineFrozenProfileEnergy_eq_zero_without_responseData (hzero : beta n = 0) :
    FrozenEnergy = 0 := by
  have hr : kernelRightVariationRate (beta n) = 0 := by rw [hzero, kernelRightVariationRate_zero]
  have h := fineFrozenProfileEnergy_le_l2Envelope (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  have hle : FrozenEnergy ≤ 0 := by
    simpa only [hr, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero] using h
  apply le_antisymm hle
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_nonneg Hn 2 Pos (beta n) (hbeta n) FrozenVec

end FrozenFamily

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
