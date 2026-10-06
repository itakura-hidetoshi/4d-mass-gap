import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointBCFApproximationMajorant

/-!
# Initial-energy floor of the actual chronological prefix majorant

A target absent from a prefix has not yet undergone the zero-diagonal update.
Its NONNEGATIVE MAJORANT can only increase along that prefix. This is not a
lower bound for the true oscillation, posterior residual, or genuine profile.

For the actual canonical prefixes, delta_v(e) >= v(e). Hence their full
normalized squared majorant includes every initial support contribution.
The unconditional fallback v(e)=2||O||_sup therefore has an explicit link-count
floor. On the original joint probability space its BCF approximation majorant
is at least ||f||_2^2, and O=0 attains that value. Optimizing this particular
fallback cannot improve the trivial norm bound. Sharper initial profiles and
other majorants are not excluded; no frozen-vector or continuum no-go is claimed.
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

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "BCFRep" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF H N hN beta hbeta
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy H
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData H N hN beta hbeta
local notation "Delta" => posteriorSixColorVariationProfile H N hN beta hbeta
local notation "Majorant" => bcfApproximationMajorant H N hN beta hbeta

/-- A fresh target retains its initial majorant, even if other links repeat. -/
theorem posteriorVariationSchedule_ge_of_not_mem (c : Link → Link → ℝ)
    (hc : ∀ target source, 0 ≤ c target source) (pre : List Link)
    (v : Link → ℝ) (hv : ∀ source, 0 ≤ v source)
    (source : Link) (hFresh : source ∉ pre) :
    v source ≤ posteriorVariationSchedule H c pre v source := by
  induction pre generalizing v with
  | nil => exact le_rfl
  | cons target pre ih =>
      have hne : source ≠ target := by
        intro h
        exact hFresh (by simp [h])
      have hTail : source ∉ pre := by
        intro h
        exact hFresh (List.mem_cons_of_mem target h)
      have hv' : ∀ e, 0 ≤ posteriorVariationStep H c v target e := by
        intro e
        unfold posteriorVariationStep
        split_ifs
        · exact le_rfl
        · exact add_nonneg (hv e) (mul_nonneg (hc target e) (hv target))
      have hHead : v source ≤ posteriorVariationStep H c v target source := by
        simp only [posteriorVariationStep, if_neg hne]
        exact le_add_of_nonneg_right (mul_nonneg (hc target source) (hv target))
      change v source ≤ posteriorVariationSchedule H c pre
        (posteriorVariationStep H c v target) source
      exact hHead.trans (ih _ hv' hTail)

/-- The zero initial majorant stays zero under every finite schedule. -/
theorem posteriorVariationSchedule_zero (c : Link → Link → ℝ) (pre : List Link) :
    posteriorVariationSchedule H c pre (fun _ => 0) = (fun _ => 0) := by
  induction pre with
  | nil => rfl
  | cons target pre ih =>
      have hStep : posteriorVariationStep H c (fun _ => 0) target = (fun _ => 0) := by
        funext source
        simp [posteriorVariationStep]
      change posteriorVariationSchedule H c pre
        (posteriorVariationStep H c (fun _ => 0) target) = _
      rw [hStep]
      exact ih

/-- Apply the constructed canonical freshness to the actual influence matrix. -/
theorem initialVariation_le_sixColorVariationProfile (R : ResponseData)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) (e : Link) :
    v e ≤ Delta R v e :=
  posteriorVariationSchedule_ge_of_not_mem H _
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_nonneg
      H beta R.epsilon R.epsilon_nonneg)
    (posteriorSixColorPrefixLinks H e) v hv e (posteriorSixColorPrefixLinks_fresh H e)

/-- This floor belongs to the upper majorant, not to genuine profile energy. -/
theorem initialOscillationEnergy_le_prefixEnergy (R : ResponseData)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) :
    OscEnergy v ≤ OscEnergy (Delta R v) := by
  unfold periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun e _ =>
    (sq_le_sq₀ (hv e) (posteriorSixColorVariationProfile_nonneg H N hN beta hbeta R v hv e)).mpr
      (initialVariation_le_sixColorVariationProfile H N hN beta hbeta R v hv e)

/-- Every selected support contribution remains in the full prefix majorant. -/
theorem initialSupportEnergy_le_prefixEnergy (R : ResponseData)
    (v : Link → ℝ) (hv : ∀ e, 0 ≤ v e) (support : Finset Link) :
    (1 / 6 : ℝ) * (∑ e ∈ support, v e ^ 2) ≤ OscEnergy (Delta R v) := by
  have hSum : (∑ e ∈ support, v e ^ 2) ≤ ∑ e : Link, v e ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ support)
      (fun e _ _ => sq_nonneg (v e))
  exact (mul_le_mul_of_nonneg_left hSum (by norm_num : (0 : ℝ) ≤ 1 / 6)).trans
    (initialOscillationEnergy_le_prefixEnergy H N hN beta hbeta R v hv)

/-- Exact cardinality coefficient in the initial uniform fallback floor. -/
theorem uniformPrefixEnergy_ge_card_mul_norm_sq (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) :
    (2 / 3 : ℝ) * (Fintype.card Link : ℝ) * ‖O‖ ^ 2 ≤
      OscEnergy (Delta R (fun _ => 2 * ‖O‖)) := by
  have hFloor := initialOscillationEnergy_le_prefixEnergy H N hN beta hbeta R
    (fun _ => 2 * ‖O‖) (fun _ => mul_nonneg (by norm_num) (norm_nonneg O))
  have hEq : OscEnergy (fun _ : Link => 2 * ‖O‖) =
      (2 / 3 : ℝ) * (Fintype.card Link : ℝ) * ‖O‖ ^ 2 := by
    unfold periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hEq] at hFloor
  exact hFloor

/-- Two explicit spatial directions at the origin exist for every natural H.
This cardinality proof uses kernel arithmetic, not a new native decision axiom. -/
theorem posteriorSpatialLink_card_ge_two : 2 ≤ Fintype.card Link := by
  let origin : PeriodicHypercubicEvenSpatialSliceVertex H := ⟨fun _ => 0, rfl⟩
  let embed : Fin 2 → Link := fun i =>
    (origin, ⟨(⟨i.val + 1, by omega⟩ : Fin 4), by
      intro heq
      have hz := congrArg Fin.val heq
      dsimp at hz
      omega⟩)
  have hInjective : Function.Injective embed := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg (fun e : Link => e.2.1.val) hij
    change i.val + 1 = j.val + 1 at hval
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective embed hInjective

/-- The original joint probability law makes the standard BCF map contractive. -/
theorem jointBCFRepresentative_norm_le_sup (O : BoundedContinuousFunction Joint ℝ) :
    ‖BCFRep O‖ ≤ ‖O‖ := by
  letI : IsProbabilityMeasure μJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  let I : BoundedContinuousFunction Joint ℝ →L[ℝ] JL2 :=
    BoundedContinuousFunction.toLp 2 μJ ℝ
  have hI : ‖I‖ ≤ 1 := by
    simpa [I, measureUnivNNReal] using
      (BoundedContinuousFunction.toLp_norm_le (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) μJ)
  calc
    ‖BCFRep O‖ ≤ ‖I‖ * ‖O‖ := I.le_opNorm O
    _ ≤ 1 * ‖O‖ := mul_le_mul_of_nonneg_right hI (norm_nonneg O)
    _ = ‖O‖ := one_mul _

/-- The uniform prefix energy already dominates the BCF sup-norm squared. -/
theorem uniformPrefixEnergy_ge_sup_norm_sq (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) :
    ‖O‖ ^ 2 ≤ OscEnergy (Delta R (fun _ => 2 * ‖O‖)) := by
  have hCard : (2 : ℝ) ≤ (Fintype.card Link : ℝ) := by
    exact_mod_cast posteriorSpatialLink_card_ge_two H
  have hFactor : (1 : ℝ) ≤ (2 / 3 : ℝ) * (Fintype.card Link : ℝ) := by linarith
  exact (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hFactor (sq_nonneg ‖O‖)).trans
      (uniformPrefixEnergy_ge_card_mul_norm_sq H N hN beta hbeta R O)

/-- No choice of approximating BCF can improve the norm bound using THIS
uniform-sup initial profile. This is not a lower bound for the genuine profile. -/
theorem norm_sq_le_uniformBCFApproximationMajorant (R : ResponseData)
    (O : BoundedContinuousFunction Joint ℝ) (f : JL2) :
    ‖f‖ ^ 2 ≤ Majorant R O (fun _ => 2 * ‖O‖) f := by
  have hRoot : ‖O‖ ≤ Real.sqrt (OscEnergy (Delta R (fun _ => 2 * ‖O‖))) := by
    simpa only [Real.sqrt_sq (norm_nonneg O)] using
      Real.sqrt_le_sqrt (uniformPrefixEnergy_ge_sup_norm_sq H N hN beta hbeta R O)
  have hTriangle : ‖f‖ ≤ ‖f - BCFRep O‖ + ‖BCFRep O‖ := by
    calc
      ‖f‖ = ‖(f - BCFRep O) + BCFRep O‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hBound := hTriangle.trans (_root_.add_le_add (le_refl ‖f - BCFRep O‖)
    ((jointBCFRepresentative_norm_le_sup H N hN beta hbeta O).trans hRoot))
  exact (sq_le_sq₀ (norm_nonneg f)
    (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mpr hBound

/-- The zero approximation attains exactly the trivial norm bound. -/
theorem uniformBCFApproximationMajorant_zero (R : ResponseData) (f : JL2) :
    Majorant R 0 (fun _ => 0) f = ‖f‖ ^ 2 := by
  simp [bcfApproximationMajorant, posteriorSixColorVariationProfile,
    posteriorVariationSchedule_zero,
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF]

/-- Exact optimum, not merely a lower estimate, of the uniform fallback family. -/
theorem norm_sq_isLeast_uniformBCFApproximationMajorants (R : ResponseData) (f : JL2) :
    IsLeast (Set.range (fun O : BoundedContinuousFunction Joint ℝ =>
      Majorant R O (fun _ => 2 * ‖O‖) f)) (‖f‖ ^ 2) := by
  constructor
  · refine ⟨0, ?_⟩
    simpa only [norm_zero, mul_zero] using uniformBCFApproximationMajorant_zero H N hN beta hbeta R f
  · rintro _ ⟨O, rfl⟩
    exact norm_sq_le_uniformBCFApproximationMajorant H N hN beta hbeta R O f

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
