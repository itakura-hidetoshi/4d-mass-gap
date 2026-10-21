import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKernelPlaquetteUniformVarianceV5_NB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorUniformLeftHaarL2FloorV5_GA
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-NC — exact ORIGINAL signed two-posterior SU(2) one-link score obstruction

NB established a spatial-volume-uniform lower variance floor for EACH
actual original SU(2) Wilson plaquette under the unchanged interacting
one-slab Wilson kernel K_b. The remaining signed GI receiver obstruction
is DIFFERENT: a real score obtained by integrating the ORIGINAL TWO
interacting Wilson conditional posterior density rows against the original
local Wilson factor and the genuine Perron joint half-density.

MQ proved this genuine compensated score depends on the source
configuration ONLY via one selected physical SU(2) spatial link e.
NC first constructs its canonical continuous function q_(H,b,e,z) on the
REAL SU(2) Haar group, and its exact Haar centered variance Q_(H,b,e,z).
Nothing is replaced by independent-Haar posterior sampling.

Using pinned mathlib variance optimal-centering, NB's original product
spatial Haar one-link refresh Fubini, and MP's TRUE original Wilson
one-link Harnack minorization, prove the quantitative receiver comparison

  exp(-8*b) * Q_(H,b,e,z) <= Var_{K_b(.,z.right)}(Psi_(H,b,e,z))

for every finite H, b>=0 and original two-boundary context z.

The result explicitly separates:
* GA: at b>0 the TWO genuine posterior rows are quantitatively
  different in SU(2)-Haar-L2 (already proved).
* NC: the actual integral transform of their contrast has score
  conditional variance bounded from below by its EXACT Haar-link
  variance, still potentially ZERO owing to genuine signed cancellation.
* Actual positive-b nonconstancy of q, GI covariance nonzero,
  volume-uniform Q floor, H1-C3 and continuum gap are NOT claimed.

No independent-Haar posterior, substitute detector, synthetic
rank assumption, Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2NC_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalSignedLinkScore
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "PsiC" => p4Q2MU_originalSignedWilsonScoreContinuous H b hb
local notation "Mass" => p4Q2MR_originalWilsonKernelMass H b
local notation "Mean" => p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "Var" => p4Q2MS_originalWilsonKernelConditionalVariance H b
local notation "ScoreVar" =>
  p4Q2MU_originalSignedScoreWilsonConditionalVariance H b hb
include hb

/-- The EXACT original signed interacting-posterior score, restricted
to the one true physical SU(2) link on which MQ proved it depends.
All surrounding source links are frozen at identity ONLY to select a
presentation; MQ proves the result is independent of this presentation.
The original two posterior laws are never changed. -/
noncomputable def p4Q2NC_originalSignedReceiverLinkScore
    (e : Link) (z : Cfg × Cfg) : C(Gauge,ℝ) := by
  let A₀ : Cfg := fun _ => 1
  have hUpdate : Continuous
      (fun g : Gauge => Function.update A₀ e g) := by
    change Continuous
      (fun g : Gauge =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H 2 A₀ e g)
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H 2 A₀ e
  exact ⟨fun g => PsiC e z (Function.update A₀ e g),
    (PsiC e z).continuous.comp hUpdate⟩

local notation "q" => p4Q2NC_originalSignedReceiverLinkScore H b hb

/-- Exact dependence of the TRUE original two-posterior signed Wilson
receiver score on ONE ORIGINAL source-side spatial link. -/
theorem p4Q2NC_originalSignedReceiverScore_eq_linkScore
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    PsiC e z A = q e z (A e) := by
  change p4Q2MQ_originalSignedLocalFiberProfile H b hb e z A =
    p4Q2MQ_originalSignedLocalFiberProfile H b hb e z
      (Function.update (fun _ : Link => (1 : Gauge)) e (A e))
  apply p4Q2MQ_originalSignedLocalProfile_eq_of_sourceReceiverLink_eq
    H b hb e z
  simp

/-- Any actual update of the receiver's ORIGINAL source spatial link
sets the genuine signed score to the same SU(2) one-link function,
regardless of all other original spatial link values. -/
theorem p4Q2NC_originalSignedReceiverScore_update_eq_linkScore
    (e : Link) (z : Cfg × Cfg) (A : Cfg) (g : Gauge) :
    PsiC e z (Function.update A e g) = q e z g := by
  rw [p4Q2NC_originalSignedReceiverScore_eq_linkScore H b hb e z]
  simp

/-- The ACTUAL signed interacting-posterior receiver's single-SU(2)
centered Haar variance. It is a diagnostic of the exact integrated
signed local profile, not the L² norm of the unintegrated two
posterior density contrast. -/
noncomputable def p4Q2NC_originalSignedReceiverLinkHaarVariance
    (e : Link) (z : Cfg × Cfg) : ℝ :=
  ∫ g : Gauge,
    (q e z g - ∫ h : Gauge, q e z h ∂mu)^2 ∂mu

local notation "Q" => p4Q2NC_originalSignedReceiverLinkHaarVariance H b hb

/-- Nonnegative exact SU(2) Haar fluctuation of the real original
signed two-Wilson-posterior receiver score. -/
theorem p4Q2NC_originalSignedReceiverLinkHaarVariance_nonneg
    (e : Link) (z : Cfg × Cfg) :
    0 ≤ Q e z := by
  unfold p4Q2NC_originalSignedReceiverLinkHaarVariance
  exact integral_nonneg (fun g => sq_nonneg _)

/-- Two witnessed actual SU(2) link values that differ under the
ORIGINAL signed posterior profile force a strictly positive
single-link Haar variance by full-support normalized SU(2) Haar. -/
theorem p4Q2NC_originalSignedReceiverLinkHaarVariance_pos_of_distinct
    (e : Link) (z : Cfg × Cfg)
    (g₀ g₁ : Gauge) (hDiff : q e z g₀ ≠ q e z g₁) :
    0 < Q e z := by
  let f : C(Gauge,ℝ) := q e z
  let m : ℝ := ∫ g : Gauge, f g ∂mu
  let sq : Gauge → ℝ := fun g => (f g - m)^2
  have hsCont : Continuous sq :=
    ((f.continuous.sub continuous_const).pow 2)
  have hsInt : Integrable sq mu :=
    hsCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨g,hg⟩ : ∃ g : Gauge, f g ≠ m := by
    by_cases h0 : f g₀ = m
    · refine ⟨g₁, ?_⟩
      intro h1
      exact hDiff (h0.trans h1.symm)
    · exact ⟨g₀,h0⟩
  have hsNonzero : sq g ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr hg)
  change 0 < ∫ g : Gauge, sq g ∂mu
  exact integral_pos_of_integrable_nonneg_nonzero hsCont hsInt
    (fun g => sq_nonneg _) hsNonzero

/-- A zero SU(2) one-link Haar variance of the REAL original
interacting-posterior signed score forces pointwise constancy,
not just an almost-everywhere statement. -/
theorem p4Q2NC_originalSignedReceiverLinkHaarVariance_zero_forces_constant
    (e : Link) (z : Cfg × Cfg)
    (hZero : Q e z = 0) (g₀ g₁ : Gauge) :
    q e z g₀ = q e z g₁ := by
  by_contra hDiff
  have hPos :=
    p4Q2NC_originalSignedReceiverLinkHaarVariance_pos_of_distinct
      H b hb e z g₀ g₁ hDiff
  rw [hZero] at hPos
  exact (lt_irrefl (0 : ℝ)) hPos

/-- The ordinary Haar-variance best-center inequality, applied to
the actual SU(2) one-link continuous signed score, rather than
assuming positivity or substituting an independent posterior. -/
theorem p4Q2NC_originalSignedLinkHaar_sqResidual_ge_variance
    (e : Link) (z : Cfg × Cfg) (c : ℝ) :
    Q e z ≤ ∫ g : Gauge, (q e z g - c)^2 ∂mu := by
  let f : C(Gauge,ℝ) := q e z
  have hVar : variance (fun g : Gauge => f g) mu = Q e z := by
    rw [variance_eq_integral f.continuous.measurable.aemeasurable]
    rfl
  calc
    Q e z = variance (fun g : Gauge => f g) mu := hVar.symm
    _ = variance (fun g : Gauge => f g - c) mu :=
      (variance_sub_const f.continuous.stronglyMeasurable.aestronglyMeasurable c).symm
    _ ≤ ∫ g : Gauge, (f g - c)^2 ∂mu := by
      simpa only [Pi.pow_apply] using
        (variance_le_expectation_sq (μ := mu)
          (X := fun g : Gauge => f g - c)
          ((f.continuous.sub continuous_const).stronglyMeasurable.aestronglyMeasurable))

/-- Even with any arbitrary surrounding original SU(2) source links
and any scalar center c, Haar resampling the actual receiver source
link gives squared residual at least the SAME real q-Haar variance. -/
theorem p4Q2NC_originalSignedScore_oneLinkHaar_sqResidual_ge_variance
    (e : Link) (z : Cfg × Cfg) (A : Cfg) (c : ℝ) :
    Q e z ≤
      ∫ g : Gauge,
        (PsiC e z (Function.update A e g) - c)^2 ∂mu := by
  calc
    Q e z ≤ ∫ g : Gauge, (q e z g - c)^2 ∂mu :=
      p4Q2NC_originalSignedLinkHaar_sqResidual_ge_variance H b hb e z c
    _ = ∫ g : Gauge,
      (PsiC e z (Function.update A e g) - c)^2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with g
      rw [p4Q2NC_originalSignedReceiverScore_update_eq_linkScore H b hb e z A g]

/-- Genuine original Wilson one-link K_b weighted square residual.
The strict positive original K_b Harnack comparison supplies
an H-independent factor exp(-8b), without modifying the signed
posterior integral defining q or Psi. -/
theorem p4Q2NC_originalSignedScore_oneLinkKernel_sqResidual_lower
    (e : Link) (z : Cfg × Cfg) (A : Cfg) (c : ℝ) :
    (Real.exp (-8*b) * K A z.2) * Q e z ≤
      ∫ g : Gauge,
        (PsiC e z (Function.update A e g) - c)^2 *
          K (Function.update A e g) z.2 ∂mu := by
  let sq : Gauge → ℝ :=
    fun g => (PsiC e z (Function.update A e g) - c)^2
  let kg : Gauge → ℝ :=
    fun g => K (Function.update A e g) z.2
  have hUpdate : Continuous (fun g : Gauge => Function.update A e g) := by
    change Continuous
      (fun g : Gauge =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H 2 A e g)
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
      H 2 A e
  have hSqCont : Continuous sq :=
    (((PsiC e z).continuous.comp hUpdate).sub continuous_const).pow 2
  have hKCont : Continuous kg :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2).comp hUpdate
  have hSqInt : Integrable sq mu :=
    hSqCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWeightedInt : Integrable (fun g => sq g * kg g) mu :=
    (hSqCont.mul hKCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFactorNonneg : 0 ≤ Real.exp (-8*b) * K A z.2 :=
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  have hPoint (g : Gauge) :
      (Real.exp (-8*b) * K A z.2) * sq g ≤ sq g * kg g := by
    calc
      (Real.exp (-8*b) * K A z.2) * sq g =
          sq g * (Real.exp (-8*b) * K A z.2) := by ring
      _ ≤ sq g * kg g :=
        mul_le_mul_of_nonneg_left
          (p4Q2NB_originalKernel_sourceOneLink_pointwise_minorization
            H b hb A z.2 e g)
          (sq_nonneg _)
  have hIntegral :
      (Real.exp (-8*b) * K A z.2) * (∫ g, sq g ∂mu) ≤
        ∫ g, sq g * kg g ∂mu := by
    rw [← integral_const_mul]
    exact integral_mono (hSqInt.const_mul _) hWeightedInt hPoint
  have hHaar :
      Q e z ≤ ∫ g, sq g ∂mu :=
    p4Q2NC_originalSignedScore_oneLinkHaar_sqResidual_ge_variance
      H b hb e z A c
  calc
    (Real.exp (-8*b) * K A z.2) * Q e z ≤
        (Real.exp (-8*b) * K A z.2) * (∫ g, sq g ∂mu) :=
      mul_le_mul_of_nonneg_left hHaar hFactorNonneg
    _ ≤ ∫ g, sq g * kg g ∂mu := hIntegral

/-- MAIN original physical signed-receiver obstruction receipt:
for EVERY H,b,e,z, the genuine K_b-weighted score variance has a
QUANTITATIVE Harnack lower bound in terms of the Haar variance of
the exact ORIGINAL two-posterior integrated SU(2) link score.

This certificate is allowed to be ZERO at positive beta. Its
positivity and the GI covariance remain separate open questions. -/
theorem p4Q2NC_originalSignedScore_trueKernelVariance_ge_HaarLinkVariance
    (e : Link) (z : Cfg × Cfg) :
    Real.exp (-8*b) * Q e z ≤ ScoreVar e z := by
  let c : ℝ := Mean z (PsiC e z)
  let F : C(Cfg,ℝ) :=
    ⟨fun A => (PsiC e z A - c)^2 * K A z.2,
      (((PsiC e z).continuous.sub continuous_const).pow 2).mul
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
          H 2 b z.2)⟩
  have hFNonneg (A : Cfg) : 0 ≤ F A :=
    mul_nonneg (sq_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  have hRefresh :=
    p4Q2NB_originalSpatialHaar_integral_oneLinkRefresh H e F hFNonneg
  have hKInt : Integrable (fun A : Cfg => K A z.2) haar :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hFInt : Integrable
      (fun A : Cfg =>
        ∫ g : Gauge, F (Function.update A e g) ∂mu) haar := by
    have hUpdateCont : Continuous
        (fun p : Cfg × Gauge => Function.update p.1 e p.2) := by
      apply continuous_pi_iff.mpr
      intro i
      by_cases hi : i = e
      · subst i
        simpa [Function.update] using
          (continuous_snd : Continuous (fun p : Cfg × Gauge => p.2))
      · simpa [Function.update, hi] using
          ((continuous_apply i).comp
            (continuous_fst : Continuous (fun p : Cfg × Gauge => p.1)))
    have hJoint :
        Integrable (fun p : Cfg × Gauge =>
          F (Function.update p.1 e p.2)) (Measure.prod haar mu) :=
      (F.continuous.comp hUpdateCont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact hJoint.integral_prod_left
  have hFiber (A : Cfg) :
      (Real.exp (-8*b) * Q e z) * K A z.2 ≤
        ∫ g : Gauge, F (Function.update A e g) ∂mu := by
    have h :=
      p4Q2NC_originalSignedScore_oneLinkKernel_sqResidual_lower
        H b hb e z A c
    change (Real.exp (-8*b) * K A z.2) * Q e z ≤
      ∫ g : Gauge, F (Function.update A e g) ∂mu at h
    calc
      (Real.exp (-8*b) * Q e z) * K A z.2 =
          (Real.exp (-8*b) * K A z.2) * Q e z := by ring
      _ ≤ _ := h
  have hIntegral :
      (Real.exp (-8*b) * Q e z) * Mass z ≤
        ∫ A : Cfg, F A ∂haar := by
    have hMono :
        ∫ A : Cfg,
          (Real.exp (-8*b) * Q e z) * K A z.2 ∂haar ≤
        ∫ A : Cfg,
          (∫ g : Gauge, F (Function.update A e g) ∂mu) ∂haar :=
      integral_mono (hKInt.const_mul _) hFInt hFiber
    rw [integral_const_mul] at hMono
    simpa only [p4Q2MR_originalWilsonKernelMass] using
      (le_trans hMono hRefresh.le)
  have hMassPos := p4Q2MS_originalWilsonKernelMass_pos H b z
  have hDiv :
      Real.exp (-8*b) * Q e z ≤ (∫ A : Cfg, F A ∂haar) / Mass z := by
    apply (le_div_iff₀ hMassPos).2
    simpa only [mul_comm] using hIntegral
  rw [p4Q2MW_originalSignedScoreVariance_eq_actualKernelVariance H b hb e z]
  simpa only [p4Q2MS_originalWilsonKernelConditionalVariance, F,
    ContinuousMap.coe_mk, c] using hDiv

/-- An actual witness of NONCONSTANCY of the original integrated
SU(2) signed posterior score implies STRICT positivity of the
original K_b-weighted conditional signed score variance. -/
theorem p4Q2NC_originalSignedScore_trueKernelVariance_pos_of_linkWitness
    (e : Link) (z : Cfg × Cfg)
    (g₀ g₁ : Gauge) (hDiff : q e z g₀ ≠ q e z g₁) :
    0 < ScoreVar e z := by
  have hQ :=
    p4Q2NC_originalSignedReceiverLinkHaarVariance_pos_of_distinct
      H b hb e z g₀ g₁ hDiff
  have hFloor : 0 < Real.exp (-8*b) * Q e z :=
    mul_pos (Real.exp_pos _) hQ
  exact lt_of_lt_of_le hFloor
    (p4Q2NC_originalSignedScore_trueKernelVariance_ge_HaarLinkVariance
      H b hb e z)

end OriginalSignedLinkScore

/-- At the genuine SU(2) frozen b=0 endpoint the original two
interacting posteriors coincide, so the exact signed one-link
receiver score and its Haar fluctuation also vanish. -/
theorem p4Q2NC_originalSignedLinkScoreHaarVariance_zero_at_beta_zero
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2NC_originalSignedReceiverLinkHaarVariance H 0
      (le_refl (0 : ℝ)) e z = 0 := by
  have hZero :=
    p4Q2MW_originalSignedReceiverScore_zero_at_frozen_zero H e z
  unfold p4Q2NC_originalSignedReceiverLinkHaarVariance
  have hScore :
      p4Q2NC_originalSignedReceiverLinkScore H 0 (le_refl (0 : ℝ)) e z = 0 := by
    ext g
    change
      p4Q2MU_originalSignedWilsonScoreContinuous H 0
        (le_refl (0 : ℝ)) e z
          (Function.update
            (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
              (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) e g) = 0
    rw [hZero]
    simp
  rw [hScore]
  simp

/-- Both ACTUAL normalized interacting SU(2) Wilson posterior rows are
strictly separated at ANY positive beta (the established GA result),
but this FACT ALONE is not a positivity certificate for the signed
integrated one-link score Q or its GI covariance. -/
theorem p4Q2NC_originalTwoWilsonPosteriorContrastHaarSq_pos_of_beta_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b (le_of_lt hb) right e := by
  exact lt_of_lt_of_le
    (p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
      H b hb right e).1
    (p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
      H b hb right e).2

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedReceiverScore_eq_linkScore
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedReceiverScore_update_eq_linkScore
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedReceiverLinkHaarVariance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedReceiverLinkHaarVariance_pos_of_distinct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedReceiverLinkHaarVariance_zero_forces_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedLinkHaar_sqResidual_ge_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedScore_oneLinkHaar_sqResidual_ge_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedScore_oneLinkKernel_sqResidual_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedScore_trueKernelVariance_ge_HaarLinkVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedScore_trueKernelVariance_pos_of_linkWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalSignedLinkScoreHaarVariance_zero_at_beta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NC_originalTwoWilsonPosteriorContrastHaarSq_pos_of_beta_pos
