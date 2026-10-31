import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitFXMomentRayleighV5_PZ37ACF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAbsoluteCrossSmallCouplingObstructionV5_PZ37ABM

/-!
# P4-Q2-PZ37ACG — actual GI moment and the upper-only coupling obstruction

Keep the SAME centered Gauss-law source, true Wilson transfer norm, Perron
representative, both interacting posteriors and full outer pair-Haar.
ABM's actual compensated full response and true transfer minorization give
  |Delta_GI| <= exp(b B_H) P_H E_b / 2,
where P_H is the actual plaquette count, B_H the original slab action budget,
and E_b the original Harnack contrast scale. Integrating the square proves
  M(H,b,e) <= [exp(b B_H) P_H E_b / 2]^2
for EVERY actual link and positive coupling. No remote contribution is dropped.

The numerical envelope is continuous in b and zero at b=0. Thus, for any
prescribed positive coupling caps and positive moment tolerances, one can
choose a strictly positive coupling at each finite volume making ALL actual
link moments smaller than the prescribed tolerance. Under every common B>0
there is a schedule b(H)<=min(B,1/(H+1)) with M(H,b(H),e)<1/(H+1) for all e.
There is no common positive moment witness on that schedule, although ACE
and ACF still give a positive moment and a positive source-specific Rayleigh
certificate in every finite volume.

This directly concerns ACF's original unweighted GI moment, NOT ABM's
full/local absolute overlap and NOT PZ37ZA's compensated two-context energy.
It does not exclude fixed b>0 or 0<b0<=b(H)<=B. It does not imply the Rayleigh
value tends to zero, since its FX denominator also varies. No all-source
coercivity, common positive-fine interval, endpoint or continuum claim follows.
All existing sources, assumptions, public roots, workflows and pins are intact.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ACG_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACG_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACG_countable : SecondCountableTopology G := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACG_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACG_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- An upper amplitude computed from the ORIGINAL finite-volume Wilson data.
It is not a new receiver or a replacement physical normalization. -/
def p4Q2PZ37ACG_originalAmplitudeEnvelope (H : ℕ) (b : ℝ) : ℝ :=
  Real.exp (b * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
    (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) *
    (p4Q2LW_originalHarnackContrastScale b / 2)

/-- The numerical envelope for the genuine UNWEIGHTED full pair-Haar moment. -/
def p4Q2PZ37ACG_originalMomentEnvelope (H : ℕ) (b : ℝ) : ℝ :=
  (p4Q2PZ37ACG_originalAmplitudeEnvelope H b) ^ 2

theorem p4Q2PZ37ACG_originalMomentEnvelope_nonneg (H : ℕ) (b : ℝ) :
    0 ≤ p4Q2PZ37ACG_originalMomentEnvelope H b :=
  sq_nonneg _

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "M" => p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H
local instance p4Q2PZ37ACG_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACG_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Divide ABM's exact compensated full response by the TRUE positive transfer
norm, then use its proved original global-action inverse bound. -/
theorem p4Q2PZ37ACG_originalCenteredGI_abs_le_amplitude
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    |gap b hb.le f₀ e z| ≤ p4Q2PZ37ACG_originalAmplitudeEnvelope H b := by
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let n : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let F : ℝ := gap b hb.le f₀ e z
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have ht : 0 < t := p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hE : 0 ≤ E / 2 := (half_pos (p4Q2LW_originalHarnackContrastScale_pos b hb)).le
  have hScaled : t * |F| ≤ n * (E / 2) := by
    have h := p4Q2PZ37ABM_originalCompensatedFullGI_abs_le_plaquetteCount H b hb e z
    change |t * F| ≤ n * (E / 2) at h
    simpa only [abs_mul, abs_of_pos ht] using h
  have hInv : t⁻¹ ≤ Real.exp (b * B) :=
    p4Q2PZ37ABM_originalPhysicalTransferNorm_inv_le_exp_actionBudget H b hb
  change |F| ≤ Real.exp (b * B) * n * (E / 2)
  calc
    |F| = t⁻¹ * (t * |F|) := by
      rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    _ ≤ t⁻¹ * (n * (E / 2)) :=
      mul_le_mul_of_nonneg_left hScaled (inv_nonneg.mpr ht.le)
    _ ≤ Real.exp (b * B) * (n * (E / 2)) :=
      mul_le_mul_of_nonneg_right hInv (mul_nonneg hn hE)
    _ = Real.exp (b * B) * n * (E / 2) := by ring

/-- The bound is integrated over the COMPLETE original pair-Haar probability
space; integrability is supplied by ACE, not assumed or obtained by totality. -/
theorem p4Q2PZ37ACG_originalMoment_le_envelope
    (b : ℝ) (hb : 0 < b) (e : Link) :
    M b hb e ≤ p4Q2PZ37ACG_originalMomentEnvelope H b := by
  let A : ℝ := p4Q2PZ37ACG_originalAmplitudeEnvelope H b
  have hPoint (z : Cfg × Cfg) : (gap b hb.le f₀ e z) ^ 2 ≤ A ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (gap b hb.le f₀ e z))
      (p4Q2PZ37ACG_originalCenteredGI_abs_le_amplitude H b hb e z) 2
    simpa only [sq_abs] using h
  change (∫ z : Cfg × Cfg, (gap b hb.le f₀ e z) ^ 2 ∂outer) ≤ A ^ 2
  calc
    (∫ z : Cfg × Cfg, (gap b hb.le f₀ e z) ^ 2 ∂outer) ≤
        ∫ _z : Cfg × Cfg, A ^ 2 ∂outer :=
      integral_mono (p4Q2PZ37ACE_originalGapSquare_integrable H b hb e)
        (integrable_const _) hPoint
    _ = A ^ 2 := by simp

/-- Only the explicit scalar bound is made continuous. No coupling-continuous
choice of the original Perron vacuum is required. -/
theorem p4Q2PZ37ACG_originalMomentEnvelope_continuous :
    Continuous (p4Q2PZ37ACG_originalMomentEnvelope H) := by
  unfold p4Q2PZ37ACG_originalMomentEnvelope p4Q2PZ37ACG_originalAmplitudeEnvelope
    p4Q2LW_originalHarnackContrastScale p4Q2LS_originalPosteriorContrastEnvelope
  fun_prop

/-- The scalar bound vanishes at zero. The physical moment itself continues
to be used only at strictly positive coupling. -/
theorem p4Q2PZ37ACG_originalMomentEnvelope_zero :
    p4Q2PZ37ACG_originalMomentEnvelope H 0 = 0 := by
  simp [p4Q2PZ37ACG_originalMomentEnvelope, p4Q2PZ37ACG_originalAmplitudeEnvelope,
    p4Q2LW_originalHarnackContrastScale, p4Q2LS_originalPosteriorContrastEnvelope]

/-- At every finite original volume one positive coupling makes ALL original
link moments smaller than any prescribed positive tolerance. -/
theorem p4Q2PZ37ACG_exists_smallPositiveCoupling_allMoments_lt
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ (b : ℝ) (hb : 0 < b), b ≤ B ∧ ∀ e : Link, M b hb e < ε := by
  have hCont : ContinuousAt (p4Q2PZ37ACG_originalMomentEnvelope H) 0 :=
    (p4Q2PZ37ACG_originalMomentEnvelope_continuous H).continuousAt
  obtain ⟨δ, hδ, hNear⟩ := (Metric.continuousAt_iff.mp hCont) ε hε
  let b : ℝ := min B δ / 2
  have hMin : 0 < min B δ := lt_min hB hδ
  have hb : 0 < b := half_pos hMin
  have hbSmall : b < min B δ := half_lt_self hMin
  have hbB : b ≤ B := hbSmall.le.trans (min_le_left B δ)
  have hbδ : b < δ := hbSmall.trans_le (min_le_right B δ)
  have hDist : dist b 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hb] using hbδ
  have hEnvAbs : |p4Q2PZ37ACG_originalMomentEnvelope H b| < ε := by
    simpa only [Real.dist_eq, p4Q2PZ37ACG_originalMomentEnvelope_zero,
      sub_zero] using hNear hDist
  refine ⟨b, hb, hbB, ?_⟩
  intro e
  exact (p4Q2PZ37ACG_originalMoment_le_envelope H b hb e).trans_lt
    ((le_abs_self _).trans_lt hEnvAbs)

/-- Arbitrary positive caps and tolerances may be prescribed before choosing
one coupling per volume. The bound holds simultaneously for every true link. -/
theorem p4Q2PZ37ACG_exists_positiveCoupling_allMoments_lt_rates
    (cap ε : ℕ → ℝ) (hcap : ∀ H, 0 < cap H) (hε : ∀ H, 0 < ε H) :
    ∃ (b : ℕ → ℝ) (hb : ∀ H, 0 < b H),
      (∀ H, b H ≤ cap H) ∧
      ∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H),
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e < ε H := by
  classical
  have hEach (H : ℕ) :
      ∃ (b : ℝ) (hb : 0 < b), b ≤ cap H ∧
        ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
          p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e < ε H :=
    p4Q2PZ37ACG_exists_smallPositiveCoupling_allMoments_lt H (cap H) (hcap H) (ε H) (hε H)
  choose b hb hBound hSmall using hEach
  exact ⟨b, hb, hBound, hSmall⟩

/-- A concrete ORIGINAL-MODEL obstruction to upper-only coupling hypotheses:
no H-dependent link selection rescues a common positive unweighted GI moment
on this schedule. ACE positivity in each finite volume is retained. -/
theorem p4Q2PZ37ACG_exists_boundedPositiveCoupling_no_uniformMoment
    (B : ℝ) (hB : 0 < B) :
    ∃ (b : ℕ → ℝ) (hb : ∀ H, 0 < b H),
      (∀ H, b H ≤ B) ∧
      (∀ H, b H ≤ 1 / ((H : ℝ) + 1)) ∧
      (∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H),
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e <
          1 / ((H : ℝ) + 1)) ∧
      (∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 < p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e) ∧
      ¬ (∃ m : ℝ, 0 < m ∧ ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
        m ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e) := by
  have hRate (H : ℕ) : 0 < 1 / ((H : ℝ) + 1) := by positivity
  obtain ⟨b, hb, hCap, hSmall⟩ :=
    p4Q2PZ37ACG_exists_positiveCoupling_allMoments_lt_rates
      (fun H => min B (1 / ((H : ℝ) + 1))) (fun H => 1 / ((H : ℝ) + 1))
      (fun H => lt_min hB (hRate H)) hRate
  refine ⟨b, hb, ?_, ?_, hSmall, ?_, ?_⟩
  · intro H
    exact (hCap H).trans (min_le_left _ _)
  · intro H
    exact (hCap H).trans (min_le_right _ _)
  · intro H
    exact p4Q2PZ37ACE_exists_originalMoment_pos H (b H) (hb H)
  · rintro ⟨m, hm, hWitness⟩
    obtain ⟨H, hRateLt⟩ := exists_nat_one_div_lt hm
    obtain ⟨e, hLower⟩ := hWitness H
    exact (not_lt_of_ge hLower) ((hSmall H e).trans hRateLt)

/-- SAME schedule: positive ACF Rayleigh certificates at every finite volume
coexist with failure of its common-positive-M input. This is NOT a theorem
that R tends to zero or has no uniform lower bound. -/
theorem p4Q2PZ37ACG_exists_finitePositiveCertificates_but_no_uniformMoment
    (B : ℝ) (hB : 0 < B) :
    ∃ (b : ℕ → ℝ) (hb : ∀ H, 0 < b H),
      (∀ H, b H ≤ B) ∧
      (∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 < (p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e /
          p4Q2PZ37ACF_originalFXEnvelope (b H)) / 18 ∧
        (p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e /
          p4Q2PZ37ACF_originalFXEnvelope (b H)) / 18 ≤
          p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H)) ∧
      ¬ (∃ m : ℝ, 0 < m ∧ ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
        m ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e) := by
  obtain ⟨b, hb, hBound, _hRate, _hSmall, _hPositive, hNo⟩ :=
    p4Q2PZ37ACG_exists_boundedPositiveCoupling_no_uniformMoment B hB
  refine ⟨b, hb, hBound, ?_, hNo⟩
  intro H
  exact p4Q2PZ37ACF_exists_positive_originalMomentRayleighBound H (b H) (hb H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_originalMomentEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_originalCenteredGI_abs_le_amplitude
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_originalMoment_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_originalMomentEnvelope_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_originalMomentEnvelope_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_exists_smallPositiveCoupling_allMoments_lt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_exists_positiveCoupling_allMoments_lt_rates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_exists_boundedPositiveCoupling_no_uniformMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACG_exists_finitePositiveCertificates_but_no_uniformMoment
