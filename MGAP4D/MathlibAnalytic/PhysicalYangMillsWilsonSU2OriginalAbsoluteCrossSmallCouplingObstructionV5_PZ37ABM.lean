import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalQuantitativeOverlapEventV5_PZ37ABL
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABM — original absolute-overlap small-coupling envelope

This append-only module retains the actual Wilson kernel, physical sources,
Perron vacuum, both interacting posteriors, the transfer norm t, and every
original outer pair-Haar coordinate.  The finite source identity and the
already proved local compensated response estimate give, at every link,
plaquette, and complete boundary pair,

  |t Delta_full| <= P_H E_b/2,
  |C_p| <= t^(-1) P_H (E_b/2)^2.

The genuine global kernel minorization proves t^(-1)<=exp(b M_H), where
M_H is the original finite slab action budget.  Thus the same explicit
envelope P_H exp(b M_H) (E_b/2)^2 bounds A_p=integral |C_p|.
For fixed H the envelope is continuous in b and vanishes at zero. We
construct, below every positive common cap B, a positive coupling schedule
b(H) <= min(B,1/(H+1)) with A_p < 1/(H+1) for ALL actual e,p.
Consequently no common alpha>0 can lower-bound selected overlaps along
that schedule, while ABL still supplies a positive overlap at every finite H.

This is a genuine original-model obstruction to the upper-only coupling
hypothesis as a sufficient uniform-nonvanishing condition. It does not
rule out fixed positive coupling, does not show ABL's event-mass ratio
vanishes, and does not disprove a continuum mass gap. No lower bound is
inferred from an upper estimate; growing volume factors are kept exactly.
Full-Hilbert coercivity, common positive-fine, E/F and H1-H4 remain open.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABM_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABM_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABM_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABM_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABM_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A scalar upper envelope for every actual full/local absolute overlap at
fixed H and b.  Its only volume factors are the genuine plaquette count
and the genuine original finite-slab Wilson action budget. -/
noncomputable def p4Q2PZ37ABM_originalAbsoluteCrossEnvelope
    (H : ℕ) (b : ℝ) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) *
    Real.exp
      (b * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
    (p4Q2LW_originalHarnackContrastScale b / 2)^2

theorem p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_nonneg
    (H : ℕ) (b : ℝ) :
    0 ≤ p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b := by
  unfold p4Q2PZ37ABM_originalAbsoluteCrossEnvelope
  positivity

/-- Sum the exact original physical plaquette responses before applying
the triangle inequality.  This is an upper estimate for the actual full
centered physical response, with the original transfer norm retained. -/
theorem p4Q2PZ37ABM_originalCompensatedFullGI_abs_le_plaquetteCount
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z| ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) *
        (p4Q2LW_originalHarnackContrastScale b / 2) := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let F : ℝ := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L (p : Plaq) : ℝ :=
    t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z
  have hSum : t * F = ∑ p : Plaq, L p := by
    dsimp [F]
    rw [p4Q2PZ37ABC_originalGIGap_eq_sum_truePlaquetteContributions H b hb e z,
      Finset.mul_sum]
    apply Finset.sum_congr (by ext p; simp)
    intro p _hp
    rw [p4Q2PZ37ABD_localContribution_eq_originalPhysicalGIGap H b hb e z p]
  change |t * F| ≤ (Fintype.card Plaq : ℝ) * (E / 2)
  calc
    |t * F| = |∑ p : Plaq, L p| := congrArg abs hSum
    _ ≤ ∑ p : Plaq, |L p| := Finset.abs_sum_le_sum_abs L Finset.univ
    _ ≤ ∑ _p : Plaq, E / 2 := by
      apply Finset.sum_le_sum
      intro p _hp
      exact p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le H b hb e p z
    _ = (Fintype.card Plaq : ℝ) * (E / 2) := by simp

/-- Pointwise original full/local density bound with the exact remaining
inverse transfer norm.  No approximation t=1 is made. -/
theorem p4Q2PZ37ABM_originalCrossDensity_abs_le_transferInverse
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z| ≤
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le)⁻¹ *
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) *
        (p4Q2LW_originalHarnackContrastScale b / 2)^2 := by
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let n : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  let F : ℝ := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L : ℝ := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z
  let C : ℝ := p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z
  have ht : 0 < t := p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le
  have hE : 0 ≤ E / 2 :=
    (half_pos (p4Q2LW_originalHarnackContrastScale_pos b hb)).le
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hF : |t * F| ≤ n * (E / 2) :=
    p4Q2PZ37ABM_originalCompensatedFullGI_abs_le_plaquetteCount H b hb e z
  have hL : |t * L| ≤ E / 2 :=
    p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le H b hb e p z
  have hProduct : t * C = (t * F) * (t * L) := by
    dsimp [C, F, L, p4Q2PZ37ABH_originalCompensatedSignedCrossDensity, t]
    ring
  have hScaled : t * |C| ≤ n * (E / 2)^2 := by
    calc
      t * |C| = |t * C| := by rw [abs_mul, abs_of_pos ht]
      _ = |t * F| * |t * L| := by rw [hProduct, abs_mul]
      _ ≤ (n * (E / 2)) * (E / 2) :=
        mul_le_mul hF hL (abs_nonneg _) (mul_nonneg hn hE)
      _ = n * (E / 2)^2 := by ring
  change |C| ≤ t⁻¹ * n * (E / 2)^2
  calc
    |C| = t⁻¹ * (t * |C|) := by
      rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    _ ≤ t⁻¹ * (n * (E / 2)^2) :=
      mul_le_mul_of_nonneg_left hScaled (inv_nonneg.mpr ht.le)
    _ = t⁻¹ * n * (E / 2)^2 := by ring

/-- The original global Wilson kernel minorization controls its actual
physical transfer denominator.  The exponential depends on H exactly
through the original global finite-slab action budget. -/
theorem p4Q2PZ37ABM_originalPhysicalTransferNorm_inv_le_exp_actionBudget
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    (p4Q2LW_originalPhysicalTransferNorm H b hb.le)⁻¹ ≤
      Real.exp
        (b * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) := by
  simpa only [p4Q2LW_originalPhysicalTransferNorm,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor,
    Real.exp_neg, inv_inv] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
      H 2 (by norm_num) b hb.le)

/-- Every unchanged original signed density is bounded by the same
explicit finite-volume envelope, uniformly over its link, plaquette,
and all original boundary variables. -/
theorem p4Q2PZ37ABM_originalCrossDensity_abs_le_envelope
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z| ≤
      p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b := by
  let n : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let m : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hInv := p4Q2PZ37ABM_originalPhysicalTransferNorm_inv_le_exp_actionBudget H b hb
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc
    |p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z| ≤
        (p4Q2LW_originalPhysicalTransferNorm H b hb.le)⁻¹ * n * (E / 2)^2 :=
      p4Q2PZ37ABM_originalCrossDensity_abs_le_transferInverse H b hb e p z
    _ ≤ Real.exp (b * m) * n * (E / 2)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hInv hn) (sq_nonneg _)
    _ = p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b := by
      unfold p4Q2PZ37ABM_originalAbsoluteCrossEnvelope
      dsimp [n, E, m]
      ring

theorem p4Q2PZ37ABM_originalAbsoluteCrossMoment_nonneg
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    0 ≤ p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p := by
  unfold p4Q2PZ37ABK_originalAbsoluteCrossMoment
  exact integral_nonneg (fun _ => abs_nonneg _)

/-- Integrate the original density envelope against the complete original
pair-Haar probability measure.  This simultaneously bounds every actual
link/plaquette absolute-overlap moment at fixed H and b. -/
theorem p4Q2PZ37ABM_originalAbsoluteCrossMoment_le_envelope
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p ≤
      p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let C : Pair → ℝ := p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  let q : ℝ := p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b
  have hInt : Integrable (fun z : Pair => |C z|) μ :=
    (p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ z, |C z| ∂μ) ≤ q
  calc
    (∫ z, |C z| ∂μ) ≤ ∫ _z : Pair, q ∂μ := by
      apply integral_mono hInt (integrable_const _)
      intro z
      exact p4Q2PZ37ABM_originalCrossDensity_abs_le_envelope H b hb e p z
    _ = q := by simp


/-- The explicit actual-model envelope is continuous as a scalar function
of coupling. No continuity of the chosen Perron vector is assumed. -/
theorem p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_continuous (H : ℕ) :
    Continuous (p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H) := by
  unfold p4Q2PZ37ABM_originalAbsoluteCrossEnvelope
    p4Q2LW_originalHarnackContrastScale p4Q2LS_originalPosteriorContrastEnvelope
  fun_prop

/-- Only the scalar envelope is evaluated at zero. The original positive
coupling response is never redefined or evaluated with a forged proof. -/
theorem p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_zero (H : ℕ) :
    p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H 0 = 0 := by
  simp [p4Q2PZ37ABM_originalAbsoluteCrossEnvelope,
    p4Q2LW_originalHarnackContrastScale, p4Q2LS_originalPosteriorContrastEnvelope]

/-- Every fixed finite original volume admits a strictly positive
coupling below any prescribed positive cap at which ALL genuine
link/plaquette absolute overlaps are smaller than any chosen epsilon.
No exchange of the coupling limit and an infinite-volume limit occurs. -/
theorem p4Q2PZ37ABM_exists_smallPositiveCoupling_allAbsoluteCross_lt
    (H : ℕ) (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ (b : ℝ) (hb : 0 < b), b ≤ B ∧
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p < ε := by
  have hCont : ContinuousAt (p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H) 0 :=
    (p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_continuous H).continuousAt
  obtain ⟨δ, hδ, hNear⟩ := (Metric.continuousAt_iff.mp hCont) ε hε
  let b : ℝ := min B δ / 2
  have hMin : 0 < min B δ := lt_min hB hδ
  have hb : 0 < b := half_pos hMin
  have hbSmall : b < min B δ := half_lt_self hMin
  have hbB : b ≤ B := hbSmall.le.trans (min_le_left B δ)
  have hbδ : b < δ := hbSmall.trans_le (min_le_right B δ)
  have hDist : dist b 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hb] using hbδ
  have hEnvAbs : |p4Q2PZ37ABM_originalAbsoluteCrossEnvelope H b| < ε := by
    simpa only [Real.dist_eq, p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_zero,
      sub_zero] using hNear hDist
  refine ⟨b, hb, hbB, ?_⟩
  intro e p
  exact (p4Q2PZ37ABM_originalAbsoluteCrossMoment_le_envelope H b hb e p).trans_lt
    ((le_abs_self _).trans_lt hEnvAbs)

/-- Under any common positive upper coupling cap, construct one
strictly positive coupling schedule for which EVERY actual link and
plaquette has A < 1/(H+1). Thus the upper-only coupling condition
cannot imply the proposed all-volume uniform absolute-cross witness.
The exact original model, both posteriors, full pair-Haar, and true
transfer norm are unchanged. This does not rule out fixed b > 0. -/
theorem p4Q2PZ37ABM_exists_boundedPositiveCoupling_no_uniformAbsoluteCross
    (B : ℝ) (hB : 0 < B) :
    ∃ (b : ℕ → ℝ) (hb : ∀ H, 0 < b H),
      (∀ H, b H ≤ B) ∧
      (∀ H, b H ≤ 1 / ((H : ℝ) + 1)) ∧
      (∀ (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p <
          1 / ((H : ℝ) + 1)) ∧
      ¬ (∃ α : ℝ, 0 < α ∧ ∀ H,
        ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
          (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
          α ≤ p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p) := by
  classical
  have hEach (H : ℕ) :
      ∃ (b : ℝ) (hb : 0 < b), b ≤ min B (1 / ((H : ℝ) + 1)) ∧
        ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
          (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
          p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p <
            1 / ((H : ℝ) + 1) := by
    have hRate : 0 < 1 / ((H : ℝ) + 1) := by positivity
    exact p4Q2PZ37ABM_exists_smallPositiveCoupling_allAbsoluteCross_lt
      H (min B (1 / ((H : ℝ) + 1))) (lt_min hB hRate)
      (1 / ((H : ℝ) + 1)) hRate
  choose b hb hCap hSmall using hEach
  refine ⟨b, hb, ?_, ?_, hSmall, ?_⟩
  · intro H
    exact (hCap H).trans (min_le_left _ _)
  · intro H
    exact (hCap H).trans (min_le_right _ _)
  · rintro ⟨α, hα, hWitness⟩
    obtain ⟨H, hRate⟩ := exists_nat_one_div_lt hα
    obtain ⟨e, p, hLower⟩ := hWitness H
    exact (not_lt_of_ge hLower) ((hSmall H e p).trans hRate)

/-- The same counterexample schedule still has a strictly positive
genuine absolute overlap in EVERY finite volume by ABL. Finite-volume
positivity and failure of a common positive infimum coexist in the
unchanged interacting model, rather than merely in an abstract sequence. -/
theorem p4Q2PZ37ABM_exists_finiteVolumePositive_but_no_uniformAbsoluteCross
    (B : ℝ) (hB : 0 < B) :
    ∃ (b : ℕ → ℝ) (hb : ∀ H, 0 < b H),
      (∀ H, b H ≤ B) ∧
      (∀ H, ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        0 < p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p) ∧
      ¬ (∃ α : ℝ, 0 < α ∧ ∀ H,
        ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
          (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
          α ≤ p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p) := by
  obtain ⟨b, hb, hBnd, _hRate, _hSmall, hNo⟩ :=
    p4Q2PZ37ABM_exists_boundedPositiveCoupling_no_uniformAbsoluteCross B hB
  refine ⟨b, hb, hBnd, ?_, hNo⟩
  intro H
  exact p4Q2PZ37ABL_exists_originalPositiveAbsoluteCross H (b H) (hb H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic


#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalCompensatedFullGI_abs_le_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalCrossDensity_abs_le_transferInverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalPhysicalTransferNorm_inv_le_exp_actionBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalCrossDensity_abs_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalAbsoluteCrossMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalAbsoluteCrossMoment_le_envelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_originalAbsoluteCrossEnvelope_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_exists_smallPositiveCoupling_allAbsoluteCross_lt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_exists_boundedPositiveCoupling_no_uniformAbsoluteCross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABM_exists_finiteVolumePositive_but_no_uniformAbsoluteCross
