import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGlobalPhysicalGICrossCauchyV5_PZ37ABG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABH — original Wilson complete pair-Haar signed-tail certificate

ABG proved the true Cauchy lower certificate for the original full GI
moment using an actual transfer-compensated local/global physical
cross-correlation. It did NOT prove a volume-independent lower bound.

Here we retain ALL original Wilson/Perron/Gauss-law/two-interacting-
posterior/outer-pair-Haar data and explicitly separate the positive
and negative portions of the same transfer-compensated cross density.
We obtain an exact full-Haar signed balance, an unconditional
strictly positive balance at a genuine finite-H link and plaquette,
and a noncircular quantitative event-minus-negative-tail criterion.

An H-independent event mass rho, density amplitude delta, and signed
negative-tail upper eta with rho*delta-eta>0 would imply a uniform
lower bound on t_(H,b(H))*K_(H,b(H),e_H,p_H). Combined with ABG and
a separately bounded contrast scale, this gives a uniform original
full GI moment lower bound. The required common event/tail inputs
are NOT shown to exist for genuine Wilson across all H in this file.

This is NOT a claim of uniform source coercivity, common fine interval,
endpoint E/F, H1-H4, OS/Wightman, or the 4D continuum mass gap.
No substitute Haar posterior, non-original physical source, Dobrushin
reconstruction, sorry, admit, native_decide, or new axiom.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABH_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABH_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABH_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABH_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABH_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The true, signed, transfer-compensated full/local Gauss-law
response density, evaluated on the UNCHANGED complete original
Wilson outer pair-boundary carrier. -/
noncomputable def p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  p4Q2LW_originalPhysicalTransferNorm H b hb.le *
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z)

/-- The genuine signed original pair-Haar cross density is continuous. -/
theorem p4Q2PZ37ABH_originalSignedCrossDensity_continuous
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Continuous (p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
      H b hb e p) := by
  unfold p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
  exact continuous_const.mul
    ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e).mul
      (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le
        (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e))

/-- Integrating the signed density over ALL the original boundary
pair-Haar coordinates is precisely t*K, without a new posterior. -/
theorem p4Q2PZ37ABH_originalSignedCrossDensity_integral_eq_trueCross
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (∫ z, p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) =
      p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p := by
  unfold p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
  rw [integral_const_mul]
  rfl

/-- Exact signed positive-minus-negative-part decomposition of
the ORIGINAL integrated transfer-compensated Wilson full/local
physical cross. The negative part is not discarded. -/
theorem p4Q2PZ37ABH_originalTrueCross_eq_positive_sub_negativeHaarParts
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p =
      (∫ z, max
          (p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) -
      (∫ z, max
          (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let f : Pair → ℝ :=
    p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  have hf : Continuous f :=
    p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p
  have hPosInt : Integrable (fun z : Pair => max (f z) 0) μ :=
    (hf.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hNegInt : Integrable (fun z : Pair => max (-(f z)) 0) μ :=
    (hf.neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) :
      f z = max (f z) 0 - max (-(f z)) 0 := by
    by_cases hz : 0 ≤ f z
    · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
      ring
    · have hNonpos : f z ≤ 0 := le_of_lt (lt_of_not_ge hz)
      rw [max_eq_right hNonpos, max_eq_left (neg_nonneg.mpr hNonpos)]
      ring
  calc
    p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p =
        ∫ z, f z ∂μ :=
      (p4Q2PZ37ABH_originalSignedCrossDensity_integral_eq_trueCross
        H b hb e p).symm
    _ = ∫ z, (max (f z) 0 - max (-(f z)) 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      exact hPoint z
    _ = (∫ z, max (f z) 0 ∂μ) -
          (∫ z, max (-(f z)) 0 ∂μ) :=
      integral_sub hPosInt hNegInt

/-- True finite-volume original Wilson positive-over-negative
imbalance AFTER all outer pair-Haar variables are integrated.
This imbalance may shrink to zero with H. -/
theorem p4Q2PZ37ABH_exists_trueLinkPlaquette_positiveSignedHaarImbalance
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      (∫ z, max
          (p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) >
      (∫ z, max
          (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  obtain ⟨e, p, hK⟩ :=
    p4Q2PZ37ABE_exists_originalLink_plaquette_positiveGlobalGICross H b hb
  refine ⟨e, p, ?_⟩
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le
  have hBal :=
    p4Q2PZ37ABH_originalTrueCross_eq_positive_sub_negativeHaarParts
      H b hb e p
  have hPositive :
      0 < p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p := mul_pos ht hK
  linarith

/-- For a continuous signed signal on its ACTUAL compact probability
carrier, measurable event mass times nonnegative event amplitude,
MINUS THE INTEGRAL OF THE FULL NEGATIVE PART, bounds the total
signed expectation from below. In particular, a local same-sign
open event alone is not sufficient: its negative complement matters. -/
theorem p4Q2PZ37ABH_compactProbability_event_minus_negativeTail
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : C(X, ℝ)) (E : Set X) (hE : MeasurableSet E)
    (rho delta eta : ℝ) (hdelta : 0 ≤ delta)
    (hMass : rho ≤ μ.real E)
    (hSignal : ∀ x ∈ E, delta ≤ f x)
    (hTail : (∫ x, max (-(f x)) 0 ∂μ) ≤ eta) :
    rho * delta - eta ≤ ∫ x, f x ∂μ := by
  have hf : Integrable (fun x : X => f x) μ :=
    f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hneg : Integrable (fun x : X => max (-(f x)) 0) μ :=
    (f.continuous.neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hind : Integrable
      (fun x : X => E.indicator (fun _ : X => delta) x) μ :=
    (integrable_const delta).indicator hE
  have hPoint (x : X) :
      E.indicator (fun _ : X => delta) x ≤
        f x + max (-(f x)) 0 := by
    have hNegBound : -(f x) ≤ max (-(f x)) 0 := le_max_left _ _
    have hNonneg : (0 : ℝ) ≤ max (-(f x)) 0 := le_max_right _ _
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      linarith [hSignal x hx]
    · have hZero : E.indicator (fun _ : X => delta) x = 0 := by
        simp [hx]
      rw [hZero]
      linarith
  have hIntegral :
      (∫ x, E.indicator (fun _ : X => delta) x ∂μ) ≤
        ∫ x, (f x + max (-(f x)) 0) ∂μ := by
    apply integral_mono hind (hf.add hneg)
    intro x
    exact hPoint x
  have hIndicator :
      (∫ x, E.indicator (fun _ : X => delta) x ∂μ) =
        μ.real E * delta := by
    simpa only [smul_eq_mul] using
      (integral_indicator_const delta hE (μ := μ))
  have hMean :
      μ.real E * delta ≤
        (∫ x, f x ∂μ) + (∫ x, max (-(f x)) 0 ∂μ) := by
    rw [← hIndicator]
    simpa only [integral_add hf hneg] using hIntegral
  have hScaled : rho * delta ≤ μ.real E * delta :=
    mul_le_mul_of_nonneg_right hMass hdelta
  linarith

/-- Exact genuine Wilson criterion. All source/posterior/transfer
inputs and the original COMPLETE pair-Haar remain unmodified.
No positive signed contribution outside E is presumed; the ENTIRE
negative tail is explicitly integrated and bounded. -/
theorem p4Q2PZ37ABH_originalCross_ge_event_minus_trueSignedTail
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2))
    (hE : MeasurableSet E)
    (rho delta eta : ℝ) (hdelta : 0 ≤ delta)
    (hMass : rho ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real E)
    (hSignal : ∀ z ∈ E,
      delta ≤ p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z)
    (hTail :
      (∫ z, max
        (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z) 0
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) ≤
          eta) :
    rho * delta - eta ≤
      p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
          H b hb e p := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let F : C(Pair, ℝ) :=
    ⟨p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p,
      p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p⟩
  have hLower : rho * delta - eta ≤ ∫ z, F z ∂μ :=
    p4Q2PZ37ABH_compactProbability_event_minus_negativeTail
      μ F E hE rho delta eta hdelta hMass hSignal hTail
  calc
    rho * delta - eta ≤ ∫ z, F z ∂μ := hLower
    _ = p4Q2LW_originalPhysicalTransferNorm H b hb.le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H b hb e p :=
      p4Q2PZ37ABH_originalSignedCrossDensity_integral_eq_trueCross H b hb e p

/-- Independent uniform event/negative-tail input implies a true
volume-uniform compensated local/global physical Wilson cross.
The inputs are stated explicitly, not asserted or circularly
derived from the unknown original GI moment. -/
theorem p4Q2PZ37ABH_allVolumes_uniformTrueCross_of_eventsAndSignedTail
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (rho delta eta kappa : ℝ)
    (hdelta : 0 ≤ delta) (hBudget : kappa ≤ rho * delta - eta)
    (hWitness : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
        (E : Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)),
        MeasurableSet E ∧
        rho ≤
          (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real E ∧
        (∀ z ∈ E,
          delta ≤ p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
            H (b H) (hb H) e p z) ∧
        (∫ z, max
          (-p4Q2PZ37ABH_originalCompensatedSignedCrossDensity
            H (b H) (hb H) e p z) 0
          ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) ≤
            eta) :
    ∀ H, ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      kappa ≤
        p4Q2LW_originalPhysicalTransferNorm H (b H) (hb H).le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H (b H) (hb H) e p := by
  intro H
  obtain ⟨e, p, E, hE, hMass, hSignal, hTail⟩ := hWitness H
  refine ⟨e, p, ?_⟩
  exact hBudget.trans
    (p4Q2PZ37ABH_originalCross_ge_event_minus_trueSignedTail
      H (b H) (hb H) e p E hE rho delta eta hdelta
      hMass hSignal hTail)

/-- ABG converts a genuine uniform compensated local/global cross
into a strictly positive common ORIGINAL unweighted full GI moment
whenever a separately validated uniform contrast-scale ceiling
is supplied. Neither of these two uniform input bounds is
silently inferred from finite-H positivity. -/
theorem p4Q2PZ37ABH_allVolumes_fullGIfloor_of_trueCross_and_scaleCap
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (kappa Emax : ℝ) (hkappa : 0 < kappa) (hEmax : 0 < Emax)
    (hScale : ∀ H, p4Q2LW_originalHarnackContrastScale (b H) ≤ Emax)
    (hCross : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        kappa ≤ p4Q2LW_originalPhysicalTransferNorm H (b H) (hb H).le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H (b H) (hb H) e p) :
    0 < kappa^2 / (Emax / 2)^2 ∧
    ∀ H, ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (_p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      kappa^2 / (Emax / 2)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
          H (b H) (hb H) e := by
  have hDen : 0 < (Emax / 2)^2 := pow_pos (half_pos hEmax) 2
  refine ⟨div_pos (pow_pos hkappa 2) hDen, ?_⟩
  intro H
  obtain ⟨e, p, hLower⟩ := hCross H
  refine ⟨e, p, ?_⟩
  let s : ℝ := p4Q2LW_originalHarnackContrastScale (b H)
  let x : ℝ := p4Q2LW_originalPhysicalTransferNorm H (b H) (hb H).le *
    p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
      H (b H) (hb H) e p
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    H (b H) (hb H) e
  have hs : 0 < s := p4Q2LW_originalHarnackContrastScale_pos (b H) (hb H)
  have hsLe : s ≤ Emax := hScale H
  have hHalfLe : s / 2 ≤ Emax / 2 := by linarith
  have hScaleSq : (s / 2)^2 ≤ (Emax / 2)^2 :=
    pow_le_pow_left₀ (half_pos hs).le hHalfLe 2
  have hg : 0 ≤ g := by
    dsimp [g]
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hCS : x^2 ≤ g * (s / 2)^2 :=
    p4Q2PZ37ABG_originalCompensatedCross_sq_le_trueFullGI_scaleSq
      H (b H) (hb H) e p
  have hKSq : kappa^2 ≤ x^2 :=
    pow_le_pow_left₀ hkappa.le hLower 2
  have hBound : kappa^2 ≤ g * (Emax / 2)^2 :=
    hKSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hScaleSq hg))
  exact (div_le_iff₀ hDen).2 hBound

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_originalSignedCrossDensity_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_originalSignedCrossDensity_integral_eq_trueCross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_originalTrueCross_eq_positive_sub_negativeHaarParts
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_exists_trueLinkPlaquette_positiveSignedHaarImbalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_compactProbability_event_minus_negativeTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_originalCross_ge_event_minus_trueSignedTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_allVolumes_uniformTrueCross_of_eventsAndSignedTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABH_allVolumes_fullGIfloor_of_trueCross_and_scaleCap
