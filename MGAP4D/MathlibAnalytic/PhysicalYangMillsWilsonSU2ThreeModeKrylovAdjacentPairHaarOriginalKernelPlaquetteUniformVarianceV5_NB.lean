import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneLinkPlaquetteHaarFiberV5_NA
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# P4-Q2-NB — TRUE interacting Wilson K_b plaquette conditional variance floor

NA established an EXACT single-real-link Haar fluctuation for every actual
spatial SU(2) Wilson plaquette, with ALL other physical link values held fixed.
MP proved the original one-slab positive Wilson kernel Harnack ratio exp(8b)
under updates of ONE actual source-side spatial link.

NB combines these facts with the genuine finite product Haar one-link
refresh identity to prove the lower variance of the ORIGINAL normalized
interacting one-slab Wilson kernel section:
  Var_{K_b(.,B)}(W_(H,p)) >= exp(-8b) V_SU2 > 0
for EVERY actual finite H, real spatial SU(2) plaquette p,
arbitrary right-boundary B, and every frozen b >= 0.

The crucial single-edge mechanism is local Harnack minorization, not
a volume-dependent global positive density floor. Both ORIGINAL
interacting-Wilson posterior densities, and the Gauss-law physical
source and signed GI receiver, are entirely UNCHANGED.
The lower bound is about the POSITIVE K_b-weighted variance, and
DOES NOT imply the signed two-posterior receiver score is nonconstant,
or nonzero GI covariance, H1-C3 closure, or continuum mass gap.

No independent-Haar posterior, Dobrushin, artificial detector,
rank postulate, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section HaarBestCenter
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar Gauge

/-- Mathlib's probability variance best-center inequality for the
genuine universal SU(2) Haar Wilson class observable. It upgrades
NA's Haar-mean identity to every real centering coefficient. -/
theorem p4Q2NB_singleSU2HaarWilson_sqResidual_ge_universal
    (c : ℝ) :
    p4Q2MY_singleSU2HaarWilsonVariance ≤
      ∫ h : Gauge, (specialUnitaryWilsonPlaquetteEnergy 2 h - c)^2 ∂mu := by
  let X : Gauge → ℝ := fun h => specialUnitaryWilsonPlaquetteEnergy 2 h
  have hX : Continuous X := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have hVar :
      variance X mu = p4Q2MY_singleSU2HaarWilsonVariance := by
    rw [variance_eq_integral hX.measurable.aemeasurable]
    rfl
  calc
    p4Q2MY_singleSU2HaarWilsonVariance = variance X mu := hVar.symm
    _ = variance (fun h : Gauge => X h - c) mu :=
      (variance_sub_const hX.stronglyMeasurable.aestronglyMeasurable c).symm
    _ ≤ ∫ h : Gauge, (X h - c)^2 ∂mu := by
      simpa only [Pi.pow_apply] using
        (variance_le_expectation_sq (μ := mu)
          (X := fun h : Gauge => X h - c)
          ((hX.sub continuous_const).stronglyMeasurable.aestronglyMeasurable))

end HaarBestCenter

section OriginalOneLinkHaarBestCenter
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "mu" => normalizedCompactHaar Gauge
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H

/-- NA's EXACT one-link Haar energy test transport at an arbitrary real
center, not necessarily the original reference-Haar mean. -/
theorem p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_transport
    (p : Plaq) (A : Cfg) (c : ℝ) :
    (∫ g : Gauge,
      (w p (Function.update A (p.1,p.2.1.1) g) - c)^2 ∂mu) =
      ∫ h : Gauge, (specialUnitaryWilsonPlaquetteEnergy 2 h - c)^2 ∂mu := by
  let test : C(ℝ,ℝ) :=
    ⟨fun x => (x-c)^2,
      ((continuous_id.sub continuous_const).pow 2)⟩
  simpa only [test, ContinuousMap.coe_mk] using
    (p4Q2NA_originalPlaquette_oneLinkHaar_energyTest_transport H p A test)

/-- A single fresh ORIGINAL physical SU(2) plaquette link retains
at least the universal Haar variance about ANY real center,
including the TRUE K_b conditional mean, with no artificial source. -/
theorem p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_ge_universal
    (p : Plaq) (A : Cfg) (c : ℝ) :
    p4Q2MY_singleSU2HaarWilsonVariance ≤
      ∫ g : Gauge,
        (w p (Function.update A (p.1,p.2.1.1) g) - c)^2 ∂mu := by
  calc
    p4Q2MY_singleSU2HaarWilsonVariance ≤
        ∫ h : Gauge,
          (specialUnitaryWilsonPlaquetteEnergy 2 h - c)^2 ∂mu :=
      p4Q2NB_singleSU2HaarWilson_sqResidual_ge_universal c
    _ = _ :=
      (p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_transport H p A c).symm

end OriginalOneLinkHaarBestCenter

section ProductHaarRefresh
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "mu" => normalizedCompactHaar Gauge
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local instance p4Q2NB_linkFintype : Fintype Link := Fintype.ofFinite _

/-- The original product spatial SU(2) reference Haar law is invariant
under resampling any one genuine link by an independent Haar group value.
This is Fubini/LMarginal for the ORIGINAL entire link carrier. -/
theorem p4Q2NB_originalSpatialHaar_lintegral_oneLinkRefresh
    (target : Link) (f : Cfg → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ A : Cfg,
        (∫⁻ g : Gauge,
          f (Function.update A target g) ∂mu) ∂haar) =
      ∫⁻ A : Cfg, f A ∂haar := by
  classical
  let measures : Link → Measure Gauge := fun _ => mu
  have hUpdate : Measurable
      (fun z : Cfg × Gauge =>
        Function.update z.1 target z.2) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i = target
    · subst i
      simpa [Function.update] using
        (measurable_snd : Measurable
          (fun z : Cfg × Gauge => z.2))
    · simpa [Function.update, hi] using
        ((measurable_pi_apply i).comp
          (measurable_fst : Measurable
            (fun z : Cfg × Gauge => z.1)))
  have hJoint : Measurable
      (fun z : Cfg × Gauge =>
        f (Function.update z.1 target z.2)) :=
    hf.comp hUpdate
  have hAverage : Measurable
      (fun A : Cfg =>
        ∫⁻ g : Gauge,
          f (Function.update A target g) ∂mu) :=
    hJoint.lintegral_prod_right
  change
    (∫⁻ A : Cfg,
        (∫⁻ g : Gauge,
          f (Function.update A target g) ∂mu) ∂Measure.pi measures) =
      ∫⁻ A : Cfg, f A ∂Measure.pi measures
  apply MeasureTheory.lintegral_eq_of_lmarginal_eq
    (μ := measures) {target} hAverage hf
  ext A
  rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
  have hIdempotent (B : Cfg) (h g : Gauge) :
      Function.update (Function.update B target h) target g =
        Function.update B target g := by
    funext i
    by_cases hi : i = target
    · subst i
      simp [Function.update]
    · simp [Function.update, hi]
  simp_rw [hIdempotent]
  simp [measures]

/-- Genuine reference product Haar Fubini identity for a nonnegative
continuous real observable, via the exact pinned Mathlib ENNReal result.
Neither interacting Wilson posterior is modified. -/
theorem p4Q2NB_originalSpatialHaar_integral_oneLinkRefresh
    (target : Link) (F : C(Cfg,ℝ)) (hF : ∀ A : Cfg, 0 ≤ F A) :
    (∫ A : Cfg,
      (∫ g : Gauge,
        F (Function.update A target g) ∂mu) ∂haar) =
      ∫ A : Cfg, F A ∂haar := by
  have hUpdateCont : Continuous
      (fun z : Cfg × Gauge => Function.update z.1 target z.2) := by
    apply continuous_pi_iff.mpr
    intro i
    by_cases hi : i = target
    · subst i
      simpa [Function.update] using
        (continuous_snd : Continuous (fun z : Cfg × Gauge => z.2))
    · simpa [Function.update, hi] using
        ((continuous_apply i).comp
          (continuous_fst : Continuous (fun z : Cfg × Gauge => z.1)))
  have hJointCont : Continuous
      (fun z : Cfg × Gauge =>
        F (Function.update z.1 target z.2)) :=
    F.continuous.comp hUpdateCont
  have hJointInt : Integrable
      (fun z : Cfg × Gauge =>
        F (Function.update z.1 target z.2))
      (Measure.prod haar mu) :=
    hJointCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterInt : Integrable
      (fun A : Cfg =>
        ∫ g : Gauge, F (Function.update A target g) ∂mu) haar :=
    hJointInt.integral_prod_left
  have hInnerInt (A : Cfg) :
      Integrable (fun g : Gauge => F (Function.update A target g)) mu := by
    have hA : Continuous (fun g : Gauge => (A,g)) :=
      continuous_const.prodMk continuous_id
    exact (hJointCont.comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOuterNonneg (A : Cfg) :
      0 ≤ ∫ g : Gauge, F (Function.update A target g) ∂mu :=
    integral_nonneg (fun g => hF (Function.update A target g))
  have hLeftNonneg :
      0 ≤ ∫ A : Cfg,
        (∫ g : Gauge, F (Function.update A target g) ∂mu) ∂haar :=
    integral_nonneg hOuterNonneg
  have hRightNonneg : 0 ≤ ∫ A : Cfg, F A ∂haar :=
    integral_nonneg hF
  have hL :=
    ofReal_integral_eq_lintegral_ofReal hOuterInt
      (ae_of_all haar hOuterNonneg)
  have hR :=
    ofReal_integral_eq_lintegral_ofReal
      (F.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (ae_of_all haar hF)
  have hENN :
      ENNReal.ofReal
        (∫ A : Cfg,
          (∫ g : Gauge, F (Function.update A target g) ∂mu) ∂haar) =
      ENNReal.ofReal (∫ A : Cfg, F A ∂haar) := by
    rw [hL, hR]
    calc
      (∫⁻ A : Cfg,
        ENNReal.ofReal
          (∫ g : Gauge, F (Function.update A target g) ∂mu) ∂haar) =
        ∫⁻ A : Cfg,
          (∫⁻ g : Gauge,
            ENNReal.ofReal (F (Function.update A target g)) ∂mu) ∂haar := by
        apply lintegral_congr
        intro A
        exact
          ofReal_integral_eq_lintegral_ofReal (hInnerInt A)
            (ae_of_all mu (fun g => hF (Function.update A target g)))
      _ = ∫⁻ A : Cfg, ENNReal.ofReal (F A) ∂haar :=
        p4Q2NB_originalSpatialHaar_lintegral_oneLinkRefresh H target
          (fun A => ENNReal.ofReal (F A))
          F.continuous.measurable.ennreal_ofReal
  have hReal := congrArg ENNReal.toReal hENN
  simpa [ENNReal.toReal_ofReal hLeftNonneg,
    ENNReal.toReal_ofReal hRightNonneg] using hReal

end ProductHaarRefresh

section OriginalPositiveWilsonKernelFloor
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
include hb
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "mu" => normalizedCompactHaar Gauge
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "w" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "Mean" =>
  p4Q2MS_originalWilsonKernelConditionalMean H b
local notation "Var" =>
  p4Q2MS_originalWilsonKernelConditionalVariance H b
local notation "M" => p4Q2MR_originalWilsonKernelMass H b
local notation "V" => p4Q2MY_singleSU2HaarWilsonVariance

/-- Uniform ORIGINAL positive Wilson kernel one-link minorization,
relative to the original full SU(2) configuration itself.
The factor exp(-8b) is independent of finite spatial volume. -/
theorem p4Q2NB_originalKernel_sourceOneLink_pointwise_minorization
    (A B : Cfg) (target : Link) (g : Gauge) :
    Real.exp (-8*b) * K A B ≤ K (Function.update A target g) B := by
  have hH :=
    p4Q2MP_originalWilsonKernel_leftLink_harnack
      H b hb A B target (A target) g
  have hSelf : Function.update A target (A target) = A := by
    funext q
    by_cases hq : q = target
    · subst q
      simp [Function.update]
    · simp [Function.update, hq]
  rw [hSelf] at hH
  have hExp : Real.exp (-8*b) * Real.exp (8*b) = 1 := by
    rw [← Real.exp_add]
    have heq : -8*b + 8*b = 0 := by ring
    rw [heq, Real.exp_zero]
  calc
    Real.exp (-8*b) * K A B ≤
        Real.exp (-8*b) *
          (Real.exp (8*b) * K (Function.update A target g) B) :=
      mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
    _ = K (Function.update A target g) B := by
      rw [← mul_assoc, hExp, one_mul]

/-- Pointwise true K_b-weighted ONE-LINK integral of the squared
physical Wilson plaquette residual has the universal Haar lower bound.
The center c is arbitrary and thus may be the actual global K_b mean. -/
theorem p4Q2NB_originalPlaquette_oneLinkKernel_sqResidual_lower
    (p : Plaq) (A B : Cfg) (c : ℝ) :
    (Real.exp (-8*b) * K A B) * V ≤
      ∫ g : Gauge,
        (w p (Function.update A (p.1,p.2.1.1) g) - c)^2 *
          K (Function.update A (p.1,p.2.1.1) g) B ∂mu := by
  let target : Link := (p.1,p.2.1.1)
  let sq : Gauge → ℝ :=
    fun g => (w p (Function.update A target g) - c)^2
  let kg : Gauge → ℝ :=
    fun g => K (Function.update A target g) B
  have hUpdate : Continuous (fun g : Gauge => Function.update A target g) := by
    change Continuous
      (fun g : Gauge =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H 2 A target g)
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
      H 2 A target
  have hSqCont : Continuous sq :=
    (((w p).continuous.comp hUpdate).sub continuous_const).pow 2
  have hKCont : Continuous kg :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b B).comp hUpdate
  have hSqInt : Integrable sq mu :=
    hSqCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWeightedInt : Integrable (fun g => sq g * kg g) mu :=
    (hSqCont.mul hKCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFactorNonneg : 0 ≤ Real.exp (-8*b) * K A B :=
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A B).le
  have hPoint (g : Gauge) :
      (Real.exp (-8*b) * K A B) * sq g ≤ sq g * kg g := by
    calc
      (Real.exp (-8*b) * K A B) * sq g =
        sq g * (Real.exp (-8*b) * K A B) := by ring
      _ ≤ sq g * kg g :=
        mul_le_mul_of_nonneg_left
          (p4Q2NB_originalKernel_sourceOneLink_pointwise_minorization
            H b hb A B target g)
          (sq_nonneg _)
  have hIntegral :
      (Real.exp (-8*b) * K A B) * (∫ g, sq g ∂mu) ≤
        ∫ g, sq g * kg g ∂mu := by
    rw [← integral_const_mul]
    exact integral_mono (hSqInt.const_mul _) hWeightedInt hPoint
  have hHaar :
      V ≤ ∫ g, sq g ∂mu :=
    p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_ge_universal
      H p A c
  calc
    (Real.exp (-8*b) * K A B) * V ≤
        (Real.exp (-8*b) * K A B) * (∫ g, sq g ∂mu) :=
      mul_le_mul_of_nonneg_left hHaar hFactorNonneg
    _ ≤ ∫ g, sq g * kg g ∂mu := hIntegral

/-- MAIN: every TRUE original positive interacting SU(2) Wilson
one-slab kernel section has the SAME volume-independent quantitative
positive lower variance for EVERY genuine spatial plaquette:
  exp(-8*b) * V_SU2 ≤ Var_{K_b(.,B)}(W_(H,p)).
Neither signed interacting posterior is replaced by independent Haar.
Signed receiver nondegeneracy and its physical GI covariance are OPEN. -/
theorem p4Q2NB_originalPlaquette_trueWilsonKernelVariance_uniform_lower
    (z : Cfg × Cfg) (p : Plaq) :
    Real.exp (-8*b) * V ≤ Var z (w p) := by
  let target : Link := (p.1,p.2.1.1)
  let c : ℝ := Mean z (w p)
  let F : C(Cfg,ℝ) :=
    ⟨fun A => (w p A - c)^2 * K A z.2,
      (((w p).continuous.sub continuous_const).pow 2).mul
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
          H 2 b z.2)⟩
  have hFNonneg (A : Cfg) : 0 ≤ F A :=
    mul_nonneg (sq_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b A z.2).le
  have hRefresh :=
    p4Q2NB_originalSpatialHaar_integral_oneLinkRefresh H target F hFNonneg
  have hKInt : Integrable (fun A : Cfg => K A z.2) haar :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_right_continuous
      H 2 b z.2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hFInt : Integrable
      (fun A : Cfg =>
        ∫ g : Gauge, F (Function.update A target g) ∂mu) haar := by
    have hUpdateCont : Continuous
        (fun q : Cfg × Gauge => Function.update q.1 target q.2) := by
      apply continuous_pi_iff.mpr
      intro i
      by_cases hi : i = target
      · subst i
        simpa [Function.update] using
          (continuous_snd : Continuous (fun q : Cfg × Gauge => q.2))
      · simpa [Function.update, hi] using
          ((continuous_apply i).comp
            (continuous_fst : Continuous (fun q : Cfg × Gauge => q.1)))
    have hJoint :
        Integrable (fun q : Cfg × Gauge =>
          F (Function.update q.1 target q.2)) (Measure.prod haar mu) :=
      (F.continuous.comp hUpdateCont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact hJoint.integral_prod_left
  have hFiber (A : Cfg) :
      (Real.exp (-8*b) * V) * K A z.2 ≤
        ∫ g : Gauge, F (Function.update A target g) ∂mu := by
    have h :=
      p4Q2NB_originalPlaquette_oneLinkKernel_sqResidual_lower
        H b hb p A z.2 c
    change (Real.exp (-8*b) * K A z.2) * V ≤
      ∫ g : Gauge, F (Function.update A target g) ∂mu at h
    calc
      (Real.exp (-8*b) * V) * K A z.2 =
          (Real.exp (-8*b) * K A z.2) * V := by ring
      _ ≤ _ := h
  have hIntegral :
      (Real.exp (-8*b) * V) * M z ≤
        ∫ A : Cfg, F A ∂haar := by
    have hMono :
        ∫ A : Cfg,
          (Real.exp (-8*b) * V) * K A z.2 ∂haar ≤
        ∫ A : Cfg,
          (∫ g : Gauge, F (Function.update A target g) ∂mu) ∂haar :=
      integral_mono (hKInt.const_mul _) hFInt hFiber
    rw [integral_const_mul] at hMono
    simpa only [p4Q2MR_originalWilsonKernelMass] using
      (le_trans hMono hRefresh.le)
  have hMassPos := p4Q2MS_originalWilsonKernelMass_pos H b z
  have hMassNE : M z ≠ 0 := hMassPos.ne'
  have hDiv :
      Real.exp (-8*b) * V ≤ (∫ A : Cfg, F A ∂haar) / M z := by
    apply (le_div_iff₀ hMassPos).2
    simpa only [mul_comm] using hIntegral
  simpa only [p4Q2MS_originalWilsonKernelConditionalVariance, F,
    ContinuousMap.coe_mk, c] using hDiv

/-- The genuine positive Wilson kernel plaquette variance has an
explicit positive H-independent floor at every frozen b ≥ 0. -/
theorem p4Q2NB_originalPlaquette_trueWilsonKernelVariance_uniform_pos
    (z : Cfg × Cfg) (p : Plaq) :
    0 < Var z (w p) := by
  have hFloor :
      0 < Real.exp (-8*b) * V :=
    mul_pos (Real.exp_pos _)
      p4Q2MY_singleSU2HaarWilsonVariance_pos
  exact lt_of_lt_of_le hFloor
    (p4Q2NB_originalPlaquette_trueWilsonKernelVariance_uniform_lower
      H b hb z p)

end OriginalPositiveWilsonKernelFloor
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_singleSU2HaarWilson_sqResidual_ge_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_transport
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalPlaquette_oneLinkHaar_sqResidual_ge_universal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalSpatialHaar_lintegral_oneLinkRefresh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalSpatialHaar_integral_oneLinkRefresh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalKernel_sourceOneLink_pointwise_minorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalPlaquette_oneLinkKernel_sqResidual_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalPlaquette_trueWilsonKernelVariance_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NB_originalPlaquette_trueWilsonKernelVariance_uniform_pos
