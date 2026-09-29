import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialGroupedLinkSweep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedDefectMargin

/-!
# Volume-free ordered six-color frame relative to the retained left boundary

Group a complete right-link sweep into the SIX canonical same-color sweeps.
The full sweep contracts left-centered norm by r=sqrt(eta), while each group
moves its original input by at most (1+r) times its color-block residual.
The original-input telescope of six nonexpansive group operators gives
  (1-r)||f-Cleft f|| <= (1+r) sum_c ||f-B_c f||.
Exactly (1-r)/(1+r)=1-2Q. Cauchy-Schwarz on Fin 6, followed by the existing
1/6 normalization, yields the coefficient (1-2Q)^2/36. No link count occurs.

This is a RELATIVE six-color frame on ALL genuine joint L2, not an uncentered
physical-sector inequality or positive-beta transfer gap. The left-retained
component is not replaced by constants. The conservative coefficient 1/36 at
beta zero does not replace the older exact beta-zero 1/6 theorem.
-/

namespace MGAP4D.MathlibAnalytic

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

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
local notation "B" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2 H N hN beta hbeta
local notation "Scolor" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta
local notation "Cleft" => allRightLeftRetainedCondExpL2 H N hN beta hbeta
local notation "E6" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy H N hN beta hbeta

/-- The preceding actual renewal bound also gives a full-sweep relative norm
contraction, with the SAME eta and without an additional Poincare input. -/
theorem allLinkSweep_leftVariance_le_lossRatio_mul
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (sources : List Link) (hNodup : sources.Nodup) (hComplete : ∀ e, e ∈ sources)
    (f : JL2) :
    ‖realHilbertProjectionSweep P sources f - Cleft f‖ ^ 2 ≤
      jointLeakageLossRatio s beta * ‖f - Cleft f‖ ^ 2 := by
  have hMargin := allLinkSweep_pathLoss_ge_one_sub_lossRatio_mul_leftVariance
    H N hN beta hbeta s hs hcut sources hNodup hComplete f
  have hSplit := allLinkSweep_leftRetained_pythagoras H N hN beta hbeta sources f
  rw [allRightLeftRetained_absorb_sweep H N hN beta hbeta sources f] at hSplit
  nlinarith

private theorem spatialLink_projection_norm_le (e : Link) (f : JL2) : ‖P e f‖ ≤ ‖f‖ := by
  have hSplit := realHilbertProjection_residual_norm_sq (P e)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent H N hN beta hbeta e)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric H N hN beta hbeta e) f
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖f - P e f‖]

/-- The existing relative defect controls displacement of one whole color,
not the sum of the displacements of its individual links. -/
theorem fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) :
    ‖f - Scolor color f‖ ≤
      (1 + Real.sqrt (jointLeakageLossRatio s beta)) * ‖f - B color f‖ := by
  have hDefect := fixedColor_defect_le_lossRatio_mul_colorResidual
    H N hN beta hbeta s hs hcut color f
  have hSquare : ‖Scolor color f - B color f‖ ^ 2 ≤
      (Real.sqrt (jointLeakageLossRatio s beta) * ‖f - B color f‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (jointLeakageLossRatio_nonneg s beta)]
    exact hDefect
  have hNorm := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hSquare
  have hTriangle : ‖f - Scolor color f‖ ≤
      ‖f - B color f‖ + ‖B color f - Scolor color f‖ := by
    simpa only [dist_eq_norm] using dist_triangle f (B color f) (Scolor color f)
  calc
    _ ≤ ‖f - B color f‖ + ‖Scolor color f - B color f‖ :=
      hTriangle.trans_eq (congrArg (fun z : ℝ => ‖f - B color f‖ + z)
        (norm_sub_rev (B color f) (Scolor color f)))
    _ ≤ ‖f - B color f‖ + Real.sqrt (jointLeakageLossRatio s beta) * ‖f - B color f‖ :=
      _root_.add_le_add (le_refl _) hNorm
    _ = _ := by ring

/-- Normalized SIX-color relative Poincare with no volume/rank factor. The
only Cauchy-Schwarz sum is over Fin 6. The input is any genuine joint-L2 vector. -/
theorem sixSpatial_ordered_relativePoincare
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) :
    ((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) * ‖f - Cleft f‖ ^ 2 ≤ E6 f := by
  classical
  let q := jointLeakageSchurCoefficient s beta
  let r := Real.sqrt (jointLeakageLossRatio s beta)
  let V := ‖f - Cleft f‖
  let colors : List (Fin 6) := (Finset.univ : Finset (Fin 6)).toList
  let groups : Fin 6 → List Link := sixSpatialColorLinkList H
  let T : Fin 6 → JL2 →L[ℝ] JL2 := fun c => realHilbertProjectionSweep P (groups c)
  let S : JL2 →L[ℝ] JL2 := realHilbertProjectionSweep P (sixSpatialGroupedLinkList H)
  let a : Fin 6 → ℝ := fun c => ‖f - B (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖
  let A := ∑ c : Fin 6, a c
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have hDen : 0 < 1 - q := by dsimp [q]; linarith [hQ.2]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrFormula : r = q / (1 - q) := by
    change Real.sqrt ((q / (1 - q)) ^ 2) = q / (1 - q)
    exact Real.sqrt_sq (div_nonneg hQ.1 hDen.le)
  have hrMul : (1 - q) * r = q := by
    rw [hrFormula]
    field_simp [hDen.ne']
  have hMinus : (1 - q) * (1 - r) = 1 - 2 * q := by nlinarith [hrMul]
  have hPlus : (1 - q) * (1 + r) = 1 := by nlinarith [hrMul]
  have hV0 : 0 ≤ V := norm_nonneg _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun c _ => norm_nonneg _
  have hFull := allLinkSweep_leftVariance_le_lossRatio_mul H N hN beta hbeta s hs hcut
    (sixSpatialGroupedLinkList H) (sixSpatialGroupedLinkList_nodup H)
    (sixSpatialGroupedLinkList_complete H) f
  have hTailSquare : ‖S f - Cleft f‖ ^ 2 ≤ (r * V) ^ 2 := by
    rw [mul_pow]
    dsimp only [r]
    rw [Real.sq_sqrt (jointLeakageLossRatio_nonneg s beta)]
    exact hFull
  have hTail : ‖S f - Cleft f‖ ≤ r * V :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 hV0)).mp hTailSquare
  have hT : ∀ c x, ‖T c x‖ ≤ ‖x‖ := fun c x =>
    GroupedProjectionSweep.norm_le P (spatialLink_projection_norm_le H N hN beta hbeta) (groups c) x
  have hGroupIdentity : S f = realHilbertProjectionSweep T colors f :=
    GroupedProjectionSweep.flatMap_apply P groups colors f
  have hTelescope : ‖f - S f‖ ≤ ∑ c : Fin 6, ‖f - T c f‖ := by
    rw [hGroupIdentity]
    simpa only [colors, Finset.sum_map_toList] using
      GroupedProjectionSweep.displacement_le_sum_initial T hT colors f
  have hGroupBound : ∀ c : Fin 6, ‖f - T c f‖ ≤ (1 + r) * a c := by
    intro c
    change ‖f - realHilbertProjectionSweep P (sixSpatialColorLinkList H c) f‖ ≤ (1 + r) * a c
    rw [sixSpatialColorLinkList_sweep_eq H N hN beta hbeta c f]
    exact fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
      H N hN beta hbeta s hs hcut (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hDisplacement : ‖f - S f‖ ≤ (1 + r) * A := by
    calc
      _ ≤ ∑ c : Fin 6, ‖f - T c f‖ := hTelescope
      _ ≤ ∑ c : Fin 6, (1 + r) * a c := Finset.sum_le_sum fun c _ => hGroupBound c
      _ = _ := by rw [← Finset.mul_sum]
  have hTriangle : V ≤ ‖f - S f‖ + ‖S f - Cleft f‖ := by
    simpa only [V, dist_eq_norm] using dist_triangle f (S f) (Cleft f)
  have hRelative : (1 - r) * V ≤ (1 + r) * A := by
    nlinarith [hTriangle, hDisplacement, hTail]
  have hLinear : (1 - 2 * q) * V ≤ A := by
    have h := mul_le_mul_of_nonneg_left hRelative hDen.le
    simpa only [← mul_assoc, hMinus, hPlus, one_mul] using h
  have hCoeff0 : 0 ≤ 1 - 2 * q := by dsimp [q]; linarith [hQ.2]
  have hSquare : ((1 - 2 * q) * V) ^ 2 ≤ A ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hCoeff0 hV0) hA0).mpr hLinear
  have hCauchy : A ^ 2 ≤ 6 * ∑ c : Fin 6, a c ^ 2 := by
    simpa [A] using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin 6)) (fun _ => (1 : ℝ)) a
  have hEnergy : E6 f = (1 / 6 : ℝ) * ∑ c : Fin 6, a c ^ 2 := by
    simp only [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy,
      groundStateJointColorNormalizedResidualEnergy,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2,
      Fintype.card_fin, one_div, a]
    norm_num
  rw [hEnergy]
  change ((1 - 2 * q) ^ 2 / 36) * V ^ 2 ≤ (1 / 6 : ℝ) * ∑ c : Fin 6, a c ^ 2
  rw [mul_pow] at hSquare
  nlinarith [hSquare.trans hCauchy]

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
