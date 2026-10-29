import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHarnackBoundedCouplingBridgeV5_PZ37ABI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABJ — genuine all-plaquette physical GI response budget

The individual ABF2 ceiling would give a growing |P_H| E_b^2/4
bound by summing naively. Instead use AAI's PROVED 24-Bessel bound
for the actual centered plaquette family on the original Haar input
Hilbert space, and LW's actual transfer-compensated Wilson response
functional Q with norm <= E_b. ABD identifies each real local
Gauss-law response as Q(V_p)/2. Consequently, UNCONDITIONALLY,

  sum_p (t Delta_local,p(z))^2 <= 6 E_b^2

at EVERY genuine boundary pair z and link e, independent of H.
This uses Haar covariance ONLY for the original input source family;
NEITHER of the two interacting Wilson posterior laws is replaced.
Integrating the COMPLETE original pair-Haar gives
  sum_p Mcomp_p <= 6 E_b^2.
ABG Cauchy then yields the simultaneous genuine signed-cross budget
  sum_p (t K_p)^2 <= 6 E_b^2 G.

For ABH's SAME signed density C_p=t Delta_full Delta_local,p,
retain its full negative part N_p=integral max(-C_p,0). Prove
  N_p^2 <= G Mcomp_p,
  sum_p N_p^2 <= 6 E_b^2 G.
No original remote boundary variable or negative contribution is dropped.

These are UNCONDITIONAL model-specific upper budgets, NOT another
assumed local event or assumed uniform kappa. However the cross/tail
budgets still contain the original full GI moment G; no uniform
positive margin, kappa, G floor, full-Hilbert coercivity, common fine
interval, E/F, H1-H4 or continuum Yang-Mills gap is asserted.
Original kernel, Perron vacuum, Gauss-law sources, actual t>0 and
both interacting posteriors are unchanged. No new axiom or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABJ_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABJ_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABJ_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABJ_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABJ_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A single authentic Wilson detector has a volume-independent
TOTAL squared response to ALL genuine centered physical plaquettes.
No independence of either interacting posterior is assumed. -/
theorem p4Q2PZ37ABJ_originalAllPlaquette_pointwise_sq_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z)^2) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V : Plaq → Lp ℝ 2 Haar :=
    p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H
  let J := p4Q2JH_originalGIResponseCLM H b hb.le e z
  let Q := p4Q2LW_originalTransferCompensatedGIResponse H b hb.le e z
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  have hSyn (a : Plaq → ℝ) :
      ‖∑ p : Plaq, a p • V p‖^2 ≤ 24 * ∑ p : Plaq, (a p)^2 := by
    -- AAI and AAX2 construct different Fintype instances on the same
    -- original vertex type. Their univ finsets coincide extensionally,
    -- but they are not definitionally equal (Fintype is data, not Prop).
    have hSynthesis :
        (∑ p : Plaq, a p • V p) =
          p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H a := by
      unfold p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis
      apply Finset.sum_congr (Finset.ext (fun p => by simp))
      intro p _hp
      rfl
    rw [hSynthesis]
    convert (p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis_sq_le H a)
      using 1
    · congr 1
      apply Finset.sum_congr (Finset.ext (fun p => by simp))
      intro p _hp
      rfl
  have hBessel : (∑ p : Plaq, (Q (V p))^2) ≤ 24 * ‖Q‖^2 :=
    finiteRealHilbert_functional_sq_sum_le_of_synthesis
      V 24 (by norm_num) hSyn Q
  have hQ : ‖Q‖ ≤ E :=
    p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb.le e z
  have hQSq : ‖Q‖^2 ≤ E^2 :=
    pow_le_pow_left₀ (norm_nonneg Q) hQ 2
  have hBudget : (∑ p : Plaq, (Q (V p))^2) ≤ 24 * E^2 :=
    hBessel.trans (mul_le_mul_of_nonneg_left hQSq (by norm_num))
  have hExact (p : Plaq) :
      t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z =
        (1 / 2 : ℝ) * Q (V p) := by
    rw [← p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap
      H b hb e z p]
    change t * ((1 / 2 : ℝ) * J (V p)) =
      (1 / 2 : ℝ) * (t * J (V p))
    ring
  calc
    (∑ p : Plaq,
      (t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z)^2) =
        (1 / 4 : ℝ) * ∑ p : Plaq, (Q (V p))^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [hExact p]
      ring
    _ ≤ (1 / 4 : ℝ) * (24 * E^2) :=
      mul_le_mul_of_nonneg_left hBudget (by norm_num)
    _ = 6 * E^2 := by ring

/-- Integrate every original boundary coordinate BEFORE summing
actual local physical moments. The total, not just each summand,
has the same coupling-only ceiling independent of the volume. -/
theorem p4Q2PZ37ABJ_originalAllPlaquette_compensatedMoment_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let f (p : Plaq) (z : Pair) : ℝ :=
    (t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z)^2
  have hCont (p : Plaq) : Continuous (f p) :=
    (continuous_const.mul
      (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e)).pow 2
  have hInt (p : Plaq) : Integrable (f p) μ :=
    (hCont p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTotalInt : Integrable (fun z : Pair => ∑ p : Plaq, f p z) μ :=
    (continuous_finset_sum Finset.univ (fun p _hp => hCont p)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∑ p : Plaq, ∫ z, f p z ∂μ) ≤ 6 * E^2
  calc
    (∑ p : Plaq, ∫ z, f p z ∂μ) =
        ∫ z, ∑ p : Plaq, f p z ∂μ := by
      rw [integral_finset_sum (Finset.univ : Finset Plaq) (fun p _hp => hInt p)]
    _ ≤ ∫ _z : Pair, 6 * E^2 ∂μ := by
      apply integral_mono hTotalInt (integrable_const _)
      intro z
      exact p4Q2PZ37ABJ_originalAllPlaquette_pointwise_sq_sum_le H b hb e z
    _ = 6 * E^2 := by simp

/-- Simultaneous real full-Haar signed physical correlations have
an l2 budget with no growing plaquette-count factor. G is the SAME
original unweighted full GI moment, not an assumed positive floor. -/
theorem p4Q2PZ37ABJ_originalAllPlaquette_compensatedCross_sq_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 *
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let M := p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e
  have hg : 0 ≤ g := by
    dsimp [g]
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∑ p : Plaq,
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2) ≤
        ∑ p : Plaq, g * M p := by
      apply Finset.sum_le_sum
      intro p _hp
      exact p4Q2PZ37ABG_originalTrueCompensatedCross_sq_le_GI_mul_localMoment H b hb e p
    _ = g * ∑ p : Plaq, M p := (Finset.mul_sum _ _ _).symm
    _ ≤ g * (6 * E^2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37ABJ_originalAllPlaquette_compensatedMoment_sum_le H b hb e) hg
    _ = 6 * E^2 * g := by ring

/-- Genuine negative part of a continuous cross product is bounded
by real L2 Cauchy-Schwarz on its unchanged compact probability carrier.
No sign assumption is imposed outside any local event. -/
theorem p4Q2PZ37ABJ_compactProbability_negativeCrossIntegral_sq_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : C(X, ℝ)) :
    (∫ x, max (-(f x * g x)) 0 ∂μ)^2 ≤
      (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  have hNegInt : Integrable (fun x => max (-(f x * g x)) 0) μ :=
    ((f.continuous.mul g.continuous).neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsInt : Integrable (fun x => |f x| * |g x|) μ :=
    (f.continuous.abs.mul g.continuous.abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hNegNonneg : 0 ≤ ∫ x, max (-(f x * g x)) 0 ∂μ :=
    integral_nonneg (fun x => le_max_right _ _)
  have hLe :
      (∫ x, max (-(f x * g x)) 0 ∂μ) ≤ ∫ x, |f x| * |g x| ∂μ := by
    apply integral_mono hNegInt hAbsInt
    intro x
    apply max_le
    · calc
        -(f x * g x) ≤ |f x * g x| := neg_le_abs _
        _ = |f x| * |g x| := abs_mul _ _
    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  let F : C(X, ℝ) := ⟨fun x => |f x|, f.continuous.abs⟩
  let L : C(X, ℝ) := ⟨fun x => |g x|, g.continuous.abs⟩
  have hCS := p4Q2PZ37ABG_compactProbability_integral_cross_sq_le μ F L
  change (∫ x, |f x| * |g x| ∂μ)^2 ≤
    (∫ x, |f x|^2 ∂μ) * (∫ x, |g x|^2 ∂μ) at hCS
  simp only [sq_abs] at hCS
  exact (pow_le_pow_left₀ hNegNonneg hLe 2).trans hCS

/-- The ENTIRE original negative signed pair-Haar contribution of
one genuine centered local physical plaquette to the full GI source. -/
noncomputable def p4Q2PZ37ABJ_originalFullNegativeCrossTail
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∫ z, max
    (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- No negative original remote contribution is discarded: the true
negative tail square is at most the full original G times the actual
compensated local original pair-Haar L2 moment. -/
theorem p4Q2PZ37ABJ_originalNegativeCrossTail_sq_le_fullGI_mul_localMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p)^2 ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let F : C(Pair, ℝ) :=
    ⟨fun z => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z,
      p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e⟩
  let L : C(Pair, ℝ) :=
    ⟨fun z => t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z,
      continuous_const.mul
        (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e)⟩
  have hProduct (z : Pair) :
      p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z =
        F z * L z := by
    dsimp [p4Q2PZ37ABH_originalCompensatedSignedCrossDensity, F, L, t]
    ring
  have hN : p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p =
      ∫ z, max (-(F z * L z)) 0 ∂μ := by
    unfold p4Q2PZ37ABJ_originalFullNegativeCrossTail
    apply integral_congr_ae
    filter_upwards with z
    rw [hProduct z]
  rw [hN]
  exact p4Q2PZ37ABJ_compactProbability_negativeCrossIntegral_sq_le μ F L

/-- Simultaneous budget for the full signed negative tails of ALL
actual centered plaquettes after ALL original pair-Haar integrations.
The coefficient is independent of H, but the original G is retained;
this does not supply the independent positive ABH margin. -/
theorem p4Q2PZ37ABJ_originalAllPlaquette_negativeTail_sq_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      (p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p)^2) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 *
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let M := p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e
  have hg : 0 ≤ g := by
    dsimp [g]
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∑ p : Plaq, (p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p)^2) ≤
        ∑ p : Plaq, g * M p := by
      apply Finset.sum_le_sum
      intro p _hp
      exact p4Q2PZ37ABJ_originalNegativeCrossTail_sq_le_fullGI_mul_localMoment H b hb e p
    _ = g * ∑ p : Plaq, M p := (Finset.mul_sum _ _ _).symm
    _ ≤ g * (6 * E^2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37ABJ_originalAllPlaquette_compensatedMoment_sum_le H b hb e) hg
    _ = 6 * E^2 * g := by ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_originalAllPlaquette_pointwise_sq_sum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_originalAllPlaquette_compensatedMoment_sum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_originalAllPlaquette_compensatedCross_sq_sum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_compactProbability_negativeCrossIntegral_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_originalNegativeCrossTail_sq_le_fullGI_mul_localMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABJ_originalAllPlaquette_negativeTail_sq_sum_le
