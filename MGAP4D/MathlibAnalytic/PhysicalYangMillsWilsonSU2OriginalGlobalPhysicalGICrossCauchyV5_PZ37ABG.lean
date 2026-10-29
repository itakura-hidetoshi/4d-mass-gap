import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCompensatedLocalPhysicalGIEnvelopeV5_PZ37ABF2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABG — true full-pair-Haar Cauchy/Schwarz bound for the
# ORIGINAL centered global/local Gauss-law Wilson physical GI response

ABE proved K_(H,b,e,p) = ∫ originalFullGI · originalLocalPhysicalGI_p
over the unchanged complete original outer pair-Haar boundary measure,
and ABF2 proved the ORIGINAL physically centered single-plaquette
local response multiplied by the actual true physical one-slab
transfer norm t_(H,b)=||T||>0 has a true full-pair-Haar L² moment
<= (E_b/2)², with E_b = exp(8b)*(exp(16b)-exp(-16b)).
Both actual distinct INTERACTING Wilson posteriors, true Perron vacuum,
unchanged Gauss-law physical source and original pair-Haar are retained.

We apply compact-probability Haar L² REAL Cauchy-Schwarz, not a
surrogate independent Haar conditional probability, to obtain:
  (t_(H,b) * K_(H,b,e,p))²
    <= G_(H,b,e) * Mcomp_(H,b,e,p)
    <= G_(H,b,e) * (E_b/2)².
The ACTUAL source-specific full unweighted original GI moment G
therefore has the model-real lower bound
  (t_(H,b) * K_(H,b,e,p))² / (E_b/2)² <= G_(H,b,e)
for every true H,b>0, e, p, not merely a new conditional assumption.

ABE provides, for every fixed H,b>0, an ACTUAL link and plaquette
with K>0; hence this explicit correlation-derived lower bound is
strictly positive for every genuine finite H.

CRITICAL: t_(H,b), K_(H,b,e,p) may depend strongly on H. This does
not establish an H-independent positive G, a bound on the signed
full residual in absolute value, or a 4D continuum mass gap.
No transfer normalization silently set to 1, no Wilson or posterior
replacement, no Dobrushin, sorry/admit/native_decide, additional
axioms, JL legacy axioms, common positive-fine interval, E/F or H1–H4.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABG_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABG_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABG_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABG_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABG_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- REAL Cauchy-Schwarz for continuous integrands on their genuine
compact probability Haar carrier; proved directly from the existing
real Haar L² Hilbert inner product, without introducing a conditional
independence hypothesis. -/
theorem p4Q2PZ37ABG_compactProbability_integral_cross_sq_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : C(X, ℝ)) :
    (∫ x, f x * g x ∂μ)^2 ≤
      (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  let F : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ f
  let L : Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ g
  have hInner :
      (∫ x, f x * g x ∂μ) = inner ℝ F L := by
    calc
      (∫ x, f x * g x ∂μ) =
          ∫ x, g x * f x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = inner ℝ F L :=
        (MeasureTheory.ContinuousMap.inner_toLp μ f g).symm
  have hF :
      ‖F‖^2 = ∫ x, (f x)^2 ∂μ := by
    calc
      ‖F‖^2 = inner ℝ F F :=
        (real_inner_self_eq_norm_sq F).symm
      _ = ∫ x, f x * f x ∂μ :=
        MeasureTheory.ContinuousMap.inner_toLp μ f f
      _ = ∫ x, (f x)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
  have hL :
      ‖L‖^2 = ∫ x, (g x)^2 ∂μ := by
    calc
      ‖L‖^2 = inner ℝ L L :=
        (real_inner_self_eq_norm_sq L).symm
      _ = ∫ x, g x * g x ∂μ :=
        MeasureTheory.ContinuousMap.inner_toLp μ g g
      _ = ∫ x, (g x)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
  have hCS : |inner ℝ F L| ≤ ‖F‖ * ‖L‖ :=
    abs_real_inner_le_norm F L
  have hSq :
      (inner ℝ F L)^2 ≤ (‖F‖ * ‖L‖)^2 := by
    calc
      (inner ℝ F L)^2 = |inner ℝ F L|^2 := (sq_abs _).symm
      _ ≤ (‖F‖ * ‖L‖)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) hCS 2
  calc
    (∫ x, f x * g x ∂μ)^2 = (inner ℝ F L)^2 := by rw [hInner]
    _ ≤ (‖F‖ * ‖L‖)^2 := hSq
    _ = ‖F‖^2 * ‖L‖^2 := by ring
    _ = (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
      rw [hF, hL]

/-- Exact original physically normalized full/local correlation-square
bound by the ORIGINAL full GI squared moment and the true compensated
local full-pair-Haar squared moment. All remaining boundary Haar
variables have already been integrated. -/
theorem p4Q2PZ37ABG_originalTrueCompensatedCross_sq_le_GI_mul_localMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
          p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment
            H b hb e p := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let F : C(Pair, ℝ) :=
    ⟨fun z =>
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z,
      p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e⟩
  let L : C(Pair, ℝ) :=
    ⟨fun z =>
      t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z,
      continuous_const.mul
        (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e)⟩
  have hCS :=
    p4Q2PZ37ABG_compactProbability_integral_cross_sq_le μ F L
  have hK :
      (∫ z, F z * L z ∂μ) =
        t * p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p := by
    calc
      (∫ z, F z * L z ∂μ) =
          ∫ z, t * (F z *
            p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
              H b hb.le
              (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
              e z) ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        change F z * (t *
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le
            (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p)
            e z) = _
        ring
      _ = t * p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H b hb e p := by
        rw [integral_const_mul]
        rfl
  rw [hK] at hCS
  exact hCS

/-- True original Wilson Cauchy-Schwarz with an EXPLICIT
H-independent coupling-only upper coefficient, but with the
actual physical transfer norm on its ORIGINAL global correlation. -/
theorem p4Q2PZ37ABG_originalCompensatedCross_sq_le_trueFullGI_scaleSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
          (p4Q2LW_originalHarnackContrastScale b / 2)^2 := by
  have hCS :=
    p4Q2PZ37ABG_originalTrueCompensatedCross_sq_le_GI_mul_localMoment
      H b hb e p
  have hM :=
    p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment_le_uniform
      H b hb e p
  have hG : 0 ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  exact hCS.trans (mul_le_mul_of_nonneg_left hM hG)

/-- Direct true model-specific positive Wilson GI full-Haar
lower criterion in terms of one genuine physically normalized
local/global signed cross-correlation. NO source-unknown Rayleigh
quantity enters the numerator. The denominator uses only the actual
frozen coupling b; the genuine volume-varying t is retained. -/
theorem p4Q2PZ37ABG_originalFullGIMoment_ge_crossSq_div_scaleSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2 /
        (p4Q2LW_originalHarnackContrastScale b / 2)^2 ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  let a : ℝ := (p4Q2LW_originalHarnackContrastScale b / 2)^2
  have ha : 0 < a :=
    pow_pos (half_pos (p4Q2LW_originalHarnackContrastScale_pos b hb)) 2
  have hBound :=
    p4Q2PZ37ABG_originalCompensatedCross_sq_le_trueFullGI_scaleSq
      H b hb e p
  apply (div_le_iff₀ ha).2
  change
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2 ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e * a
  exact hBound

/-- The ABE genuine physical positive-global-correlation plaquette
supplies a strictly positive explicit Cauchy/Schwarz lower
certificate for the unchanged original full GI moment at EVERY
finite H,b>0. No H-independent positive infimum is claimed. -/
theorem p4Q2PZ37ABG_exists_trueLinkPlaquette_positive_crossDerivedGIfloor
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 <
        (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H b hb e p)^2 /
          (p4Q2LW_originalHarnackContrastScale b / 2)^2 ∧
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p)^2 /
          (p4Q2LW_originalHarnackContrastScale b / 2)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  obtain ⟨e, p, hK⟩ :=
    p4Q2PZ37ABE_exists_originalLink_plaquette_positiveGlobalGICross H b hb
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le
  have hE := p4Q2LW_originalHarnackContrastScale_pos b hb
  refine ⟨e, p, ?_, p4Q2PZ37ABG_originalFullGIMoment_ge_crossSq_div_scaleSq
    H b hb e p⟩
  exact div_pos (pow_pos (mul_pos ht hK) 2)
    (pow_pos (half_pos hE) 2)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABG_compactProbability_integral_cross_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABG_originalTrueCompensatedCross_sq_le_GI_mul_localMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABG_originalCompensatedCross_sq_le_trueFullGI_scaleSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABG_originalFullGIMoment_ge_crossSq_div_scaleSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABG_exists_trueLinkPlaquette_positive_crossDerivedGIfloor
