import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonStrongHaarL2DerivativeV5_JG
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-JH: original interacting Wilson fiber as a bounded Haar-L2 functional

Fix the REAL finite SU(2) lattice, frozen Wilson coupling, physical link,
and full left/right boundary context. The original GN fiber response is
an iterated Haar integral of the actual frozen Wilson kernel against the
actual difference of two interacting posterior densities, divided by the
actual joint square-root density. Integrate these fixed factors into a
continuous spatial-source kernel. Its genuine Haar-L2 vector represents
one bounded real-linear functional by the L2 inner product.

For continuous representatives, Fubini proves exact equality with the
original GN fiber integral, including every original density factor.
The strong Haar-L2 derivative proved in JG therefore passes through this
REAL Wilson response. The fine-beta tangent is the original spatial
Wilson action, not a synthetic source or an independent posterior.

No nonzero second-context response is assumed or proved merely from
nonconstancy of the tangent. Frozen beta is distinct from the varying
fine beta. No H-uniform window, H1-C3, or continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section FixedOriginalWilson

variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "delta" => p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb

/-- Continuity of the actual inverse joint square-root density follows
from the existing physical BCF normalization identity, without changing
that density or introducing a different posterior. -/
theorem p4Q2JH_originalInverseJointSqrt_continuous :
    Continuous (fun z : Cfg × Cfg => (s z)⁻¹) := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖⁻¹
  let w := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H 2 (by norm_num) b hb
  let v := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H 2 (by norm_num) b hb
  have hL : L ≠ 0 := inv_ne_zero
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b hb).ne'
  have hc : Continuous (fun z : Cfg × Cfg => (w z * v z.2) / L) :=
    (w.continuous.mul (v.continuous.comp continuous_snd)).div_const L
  have heq : (fun z : Cfg × Cfg => (w z * v z.2) / L) =
      (fun z : Cfg × Cfg => (s z)⁻¹) := by
    funext z
    have h := p4Q2GN_originalDensityCancellationWeight_eq H b hb z
    change w z * v z.2 = L / s z at h
    rw [h]
    field_simp [hL]
  rw [heq] at hc
  exact hc

/-- The ORIGINAL fixed Wilson fiber kernel, with its original joint
density and interacting posterior contrast still present. The second
argument is the genuine source spatial configuration, not a mode index. -/
noncomputable def p4Q2JH_originalFiberKernel
    (e : Link) (z : Cfg × Cfg) : C(Gauge × Cfg, ℝ) := by
  classical
  refine ⟨(fun p => K p.2 (Function.update z.2 e p.1) *
    (s (z.1, Function.update z.2 e p.1))⁻¹ * delta z.2 e p.1), ?_⟩
  have hUp : Continuous (fun p : Gauge × Cfg => Function.update z.2 e p.1) := by
    fun_prop
  have hK := (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
    H 2 b).comp (continuous_snd.prodMk hUp)
  have hs : Continuous (fun p : Gauge × Cfg =>
      (s (z.1, Function.update z.2 e p.1))⁻¹) :=
    (p4Q2JH_originalInverseJointSqrt_continuous H b hb).comp
      (continuous_const.prodMk hUp)
  have hd := (p4Q2GN_originalDensityContrast_continuous H b hb z.2 e).comp
    continuous_fst
  exact (hK.mul hs).mul hd

/-- A genuine continuous spatial-source representer obtained by Bochner
integration over the physical SU(2) link variable. -/
noncomputable def p4Q2JH_originalFiberRepresenter
    (e : Link) (z : Cfg × Cfg) : C(Cfg, ℝ) :=
  ∫ g : Gauge, (p4Q2JH_originalFiberKernel H b hb e z).curry g ∂nu

theorem p4Q2JH_originalFiberRepresenter_apply
    (e : Link) (z : Cfg × Cfg) (A : Cfg) :
    p4Q2JH_originalFiberRepresenter H b hb e z A =
      ∫ g : Gauge, p4Q2JH_originalFiberKernel H b hb e z (g,A) ∂nu := by
  let k := p4Q2JH_originalFiberKernel H b hb e z
  have hi : Integrable (fun g : Gauge => k.curry g) nu :=
    k.curry.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact ContinuousMap.integral_apply hi A

/-- A bounded REAL linear functional on the actual spatial Haar-L2
carrier. Its representer contains the literal original Wilson factors;
this is not an arbitrarily chosen detector or a postulated frame. -/
noncomputable def p4Q2JH_originalFiberMomentCLM
    (e : Link) (z : Cfg × Cfg) : Lp ℝ 2 haar →L[ℝ] ℝ :=
  innerSL ℝ (ContinuousMap.toLp 2 haar ℝ
    (p4Q2JH_originalFiberRepresenter H b hb e z))

/-- Fubini identifies the bounded L2 functional with the exact original
iterated Wilson transfer and posterior-contrast Haar integral for every
continuous physical source representative. All integrals here are of
continuous functions on compact finite-measure spaces. -/
theorem p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral
    (e : Link) (z : Cfg × Cfg) (f : C(Cfg, ℝ)) :
    p4Q2JH_originalFiberMomentCLM H b hb e z
        (ContinuousMap.toLp 2 haar ℝ f) =
      ∫ g : Gauge,
        ((∫ A : Cfg, K A (Function.update z.2 e g) * f A ∂haar) /
          s (z.1, Function.update z.2 e g)) * delta z.2 e g ∂nu := by
  classical
  let k := p4Q2JH_originalFiberKernel H b hb e z
  let r := p4Q2JH_originalFiberRepresenter H b hb e z
  have hInner : p4Q2JH_originalFiberMomentCLM H b hb e z
      (ContinuousMap.toLp 2 haar ℝ f) = ∫ A : Cfg, f A * r A ∂haar := by
    change inner ℝ (ContinuousMap.toLp 2 haar ℝ r)
      (ContinuousMap.toLp 2 haar ℝ f) = _
    simpa using (ContinuousMap.inner_toLp haar r f)
  have hJoint : Continuous (fun p : Cfg × Gauge => f p.1 * k (p.2,p.1)) :=
    (f.continuous.comp continuous_fst).mul
      (k.continuous.comp (continuous_snd.prodMk continuous_fst))
  have hInt : Integrable
      (fun p : Cfg × Gauge => f p.1 * k (p.2,p.1)) (Measure.prod haar nu) :=
    hJoint.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hInner]
  calc
    (∫ A : Cfg, f A * r A ∂haar) =
        ∫ A : Cfg, ∫ g : Gauge, f A * k (g,A) ∂nu ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      have hr := p4Q2JH_originalFiberRepresenter_apply H b hb e z A
      change r A = ∫ g : Gauge, k (g,A) ∂nu at hr
      rw [hr, integral_const_mul]
    _ = ∫ g : Gauge, ∫ A : Cfg, f A * k (g,A) ∂haar ∂nu :=
      integral_integral_swap hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with g
      have hp : (fun A : Cfg => f A * k (g,A)) =
          (fun A : Cfg => (K A (Function.update z.2 e g) * f A) *
            (s (z.1, Function.update z.2 e g))⁻¹ * delta z.2 e g) := by
        funext A
        dsimp [k, p4Q2JH_originalFiberKernel]
        ring
      rw [hp, integral_mul_const, integral_mul_const]
      simp only [div_eq_mul_inv]

/-- Whenever a physical source has the specified continuous Haar-a.e.
representative, the new bounded functional is literally GN's original
interacting Wilson moment of that same physical source. -/
theorem p4Q2JH_originalFiberMomentCLM_agrees_with_physicalGN
    (e : Link) (z : Cfg × Cfg) (u : Phys) (f : C(Cfg, ℝ))
    (hu : (fun A : Cfg => (u : Lp ℝ 2 haar) A) =ᵐ[haar] f) :
    p4Q2JH_originalFiberMomentCLM H b hb e z (u : Lp ℝ 2 haar) =
      p4Q2GN_originalTransferFiberContrastMoment H b hb u e z := by
  have hLp : (u : Lp ℝ 2 haar) = ContinuousMap.toLp 2 haar ℝ f := by
    apply Lp.ext
    exact hu.trans (f.coeFn_toLp (p := 2) (𝕜 := ℝ) haar).symm
  rw [hLp, p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral]
  change (∫ g : Gauge,
    ((∫ A : Cfg, K A (Function.update z.2 e g) * f A ∂haar) /
      s (z.1, Function.update z.2 e g)) * delta z.2 e g ∂nu) =
    (∫ g : Gauge,
      (decomposableOneSliceTransferIntegral H 2 b u (Function.update z.2 e g) /
        s (z.1, Function.update z.2 e g)) * delta z.2 e g ∂nu)
  have hTransfer (B : Cfg) :
      decomposableOneSliceTransferIntegral H 2 b u B =
        ∫ A : Cfg, K A B * f A ∂haar := by
    unfold decomposableOneSliceTransferIntegral
    apply integral_congr_ae
    filter_upwards [hu] with A hA
    rw [hA]
  apply integral_congr_ae
  filter_upwards with g
  rw [hTransfer]

/-- The genuine fixed original Wilson fiber response inherits the JG
strong Haar-L2 beta derivative by the bounded-linear chain rule. The
frozen coupling b and both original posteriors are held fixed. -/
theorem p4Q2JH_originalFiberFineRow_hasDerivAt_zero
    (e : Link) (z : Cfg × Cfg) :
    HasDerivAt
      (fun t : ℝ => p4Q2JH_originalFiberMomentCLM H b hb e z
        (ContinuousMap.toLp 2 haar ℝ (p4Q2JF_originalWilsonHaarRowContinuous H t)))
      (p4Q2JH_originalFiberMomentCLM H b hb e z
        (p4Q2JE_originalWilsonHaarZeroDerivativeLp H)) 0 := by
  exact (p4Q2JH_originalFiberMomentCLM H b hb e z).hasFDerivAt.comp_hasDerivAt 0
    (p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_strongHaarL2 H)

/-- The original frozen normalization factor converts the fiber moment
back to the genuine original GI gap whenever the physical representative
hypothesis above holds. -/
noncomputable def p4Q2JH_originalGIResponseCLM
    (e : Link) (z : Cfg × Cfg) : Lp ℝ 2 haar →L[ℝ] ℝ :=
  (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖⁻¹ * s z) •
    p4Q2JH_originalFiberMomentCLM H b hb e z

theorem p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
    (e : Link) (z : Cfg × Cfg) (u : Phys) (f : C(Cfg, ℝ))
    (hu : (fun A : Cfg => (u : Lp ℝ 2 haar) A) =ᵐ[haar] f) :
    p4Q2JH_originalGIResponseCLM H b hb e z (u : Lp ℝ 2 haar) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb u e z := by
  change (-‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * s z) *
      p4Q2JH_originalFiberMomentCLM H b hb e z (u : Lp ℝ 2 haar) = _
  rw [p4Q2JH_originalFiberMomentCLM_agrees_with_physicalGN H b hb e z u f hu]
  exact (p4Q2GN_originalExpectationGap_eq_transferFiberMoment H b hb u e z).symm

/-- Differentiation through the REAL fixed GI functional, not merely an
unspecified bounded map: its actual kernel and physical agreement were
proved above. No assertion is made that the derivative is nonzero. -/
theorem p4Q2JH_originalGIFineRow_hasDerivAt_zero
    (e : Link) (z : Cfg × Cfg) :
    HasDerivAt
      (fun t : ℝ => p4Q2JH_originalGIResponseCLM H b hb e z
        (ContinuousMap.toLp 2 haar ℝ (p4Q2JF_originalWilsonHaarRowContinuous H t)))
      (p4Q2JH_originalGIResponseCLM H b hb e z
        (p4Q2JE_originalWilsonHaarZeroDerivativeLp H)) 0 := by
  exact (p4Q2JH_originalGIResponseCLM H b hb e z).hasFDerivAt.comp_hasDerivAt 0
    (p4Q2JG_originalWilsonHaarRow_hasDerivAt_zero_strongHaarL2 H)

end FixedOriginalWilson
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalInverseJointSqrt_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalFiberMomentCLM_eq_iteratedIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalFiberMomentCLM_agrees_with_physicalGN
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalFiberFineRow_hasDerivAt_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JH_originalGIFineRow_hasDerivAt_zero
