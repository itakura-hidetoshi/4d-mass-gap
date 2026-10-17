import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAnchoredPhysicalSourceFiberV5_JD
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonCrossingMeanInvariantV5_IX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

/-!
# P4-Q2-JE: true beta-zero first variation is a nonconstant physical Haar-L² profile

At every literal finite even-periodic SU(2) spatial volume H, the original
one-slab Haar row F_beta(B) is differentiable at beta=0 for EACH genuine
right physical spatial configuration B (IW).

The true crossing-action left-Haar mean is independent of B (IX). Thus
the ENTIRE first-variation function equals -W_H(B)/2 minus a genuine
boundary-independent finite Haar constant. We construct this derivative
as a continuous function on the true compact physical right SU(2) link
configuration, then embed it into the ACTUAL normalized product Haar L².

IY's genuine -I one-link primary plaquette twist gives a difference of
first-variation values of AT LEAST ONE between two ACTUAL boundaries.
Full support of the true product Haar and continuous-function-to-L²
injectivity imply that the first-variation's Haar-L² representative
cannot be a scalar constant vector.

This proves a nonconstant L² REPRESENTATIVE of the true pointwise first
variation; it does NOT YET assert HasDerivAt of the norm-valued map
beta ↦ F_beta in L², nor does it assert that the ORIGINAL interacting
GI posterior detector sees the first variation. The physical anchored
source nonzero but GI residual potentially zero remains a separate
open question. No artificial Haar conditional posterior, source frame,
Dobrushin, volume-uniform small-beta interval, H1-C3 or continuum
Yang-Mills mass-gap conclusion is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JE_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JE_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JE_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JE_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JE_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2JE_SU2_normalizedHaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance
local instance p4Q2JE_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

section OriginalWilsonFirstVariation

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "F" =>
  p4Q2IV_originalWilsonUnitHaarKernelSection H

/-- The literal physical finite-Haar constant in the original Wilson row
derivative, using the true product-Haar average of spatial Wilson action
and the true crossing action at the all-identity right boundary. -/
noncomputable def p4Q2JE_originalWilsonHaarZeroDerivativeConstant : ℝ :=
  (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) +
    (∫ A : Cfg, C A (fun _ => 1) ∂haar)

/-- The ENTIRE beta-zero first variation of the true original Wilson
Haar row as a compact-continuous function of the physical right
boundary. In particular, it is not an invented finite vector or
surrogate interacting posterior. -/
noncomputable def p4Q2JE_originalWilsonHaarZeroDerivativeProfile :
    C(Cfg, ℝ) :=
  ⟨(fun B => -(1 / 2 : ℝ) * W B -
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H),
    (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
      continuous_const⟩

/-- The genuine original Wilson Haar row is pointwise differentiable in
beta at zero, with derivative equal to our complete continuous
spatial-action profile at EACH actual right SU(2) boundary. -/
theorem p4Q2JE_originalWilsonHaarRow_hasDerivAt_zero_profile (B : Cfg) :
    HasDerivAt (fun t : ℝ => F t B)
      (p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B) 0 := by
  have hC := p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B
  have hDeriv := p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero_explicit H B
  have hEq :
      -(1 / 2 : ℝ) * W B -
          (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) -
          (∫ A : Cfg, C A B ∂haar) =
        p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B := by
    rw [hC]
    change
      -(1 / 2 : ℝ) * W B -
        (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) -
        (∫ A : Cfg, C A (fun _ => 1) ∂haar) =
      -(1 / 2 : ℝ) * W B -
        ((1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) +
          (∫ A : Cfg, C A (fun _ => 1) ∂haar))
    ring
  exact hEq ▸ hDeriv

/-- The right-boundary independent frozen Haar constant cancels
EXACTLY when comparing two genuinely physical beta-zero responses. -/
theorem p4Q2JE_originalWilsonZeroDerivativeProfile_difference
    (B₀ B₁ : Cfg) :
    p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₀ -
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₁ =
        -(1 / 2 : ℝ) * (W B₀ - W B₁) := by
  change
    (-(1 / 2 : ℝ) * W B₀ -
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) -
    (-(1 / 2 : ℝ) * W B₁ -
      p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) =
    -(1 / 2 : ℝ) * (W B₀ - W B₁)
  ring

/-- The true original derivative profile is genuinely nonconstant
on the entire physical right-boundary carrier, at every finite H. -/
theorem p4Q2JE_originalWilsonZeroDerivativeProfile_nonconstant :
    ∃ B₀ B₁ : Cfg,
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₀ ≠
        p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₁ := by
  obtain ⟨B₀, B₁, hW⟩ := p4Q2IY_originalSpatialWilsonAction_not_constant H
  refine ⟨B₀, B₁, ?_⟩
  have hdiff := p4Q2JE_originalWilsonZeroDerivativeProfile_difference H B₀ B₁
  intro hEq
  have hzero :
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₀ -
        p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₁ = 0 :=
    sub_eq_zero.mpr hEq
  rw [hdiff] at hzero
  have hWzero : W B₀ - W B₁ = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  exact hW (sub_eq_zero.mp hWzero)

/-- More quantitatively, the ORIGINAL Wilson Haar row derivative at
the literal all-one configuration exceeds its derivative at the
genuine one-primary-spatial-link -I twist by at least one. This is
a TRUE finite-volume action witness, not a uniform beta radius. -/
theorem p4Q2JE_originalWilsonZeroDerivativeProfile_centralTwist_gap_ge_one :
    (1 : ℝ) ≤
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H
        (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) -
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H
        (periodicHypercubicEvenSpatialSliceRestriction
          (p4Q2IY_onePrimaryLinkCentralTwist H)) := by
  have hDiff :=
    p4Q2JE_originalWilsonZeroDerivativeProfile_difference H
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (periodicHypercubicEvenSpatialSliceRestriction
        (p4Q2IY_onePrimaryLinkCentralTwist H))
  have h0 := p4Q2IY_allOneSpatialWilsonAction_zero H
  have hge := p4Q2IY_actualSpatialWilsonAction_twist_ge_two H
  rw [hDiff, h0]
  nlinarith

/-- A vector in the ACTUAL physical spatial Haar-L² carrier representing
the continuous pointwise beta-zero Wilson first-variation profile. It
is an L² representative of the pointwise derivative; no strong L²
differentiability is claimed solely from this definition. -/
noncomputable def p4Q2JE_originalWilsonHaarZeroDerivativeLp :
    Lp ℝ 2 haar :=
  ContinuousMap.toLp 2 haar ℝ
    (p4Q2JE_originalWilsonHaarZeroDerivativeProfile H)

/-- TRUE full-support normalized finite spatial product Haar makes the
L² first-variation profile different from EVERY constant-vector image.
This is a genuine positive physical noncollinearity statement at the
level of the first variation, not proof of its strong L² derivative. -/
theorem p4Q2JE_originalWilsonHaarZeroDerivativeLp_ne_continuousConstant
    (c : ℝ) :
    p4Q2JE_originalWilsonHaarZeroDerivativeLp H ≠
      ContinuousMap.toLp 2 haar ℝ
        (⟨fun _ : Cfg => c, continuous_const⟩ : C(Cfg, ℝ)) := by
  intro hEq
  have hCont :
      p4Q2JE_originalWilsonHaarZeroDerivativeProfile H =
        (⟨fun _ : Cfg => c, continuous_const⟩ : C(Cfg, ℝ)) :=
    (ContinuousMap.toLp_injective (p := 2) (μ := haar) (𝕜 := ℝ)) hEq
  obtain ⟨B₀, B₁, hne⟩ :=
    p4Q2JE_originalWilsonZeroDerivativeProfile_nonconstant H
  apply hne
  have h0 : p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₀ = c := by
    exact congrArg (fun f : C(Cfg, ℝ) => f B₀) hCont
  have h1 : p4Q2JE_originalWilsonHaarZeroDerivativeProfile H B₁ = c := by
    exact congrArg (fun f : C(Cfg, ℝ) => f B₁) hCont
  exact h0.trans h1.symm

/-- In particular the genuine normalized Haar-L² first-variation
representative has strictly positive norm; the no-false-frame
statement follows solely from a physical spatial plaquette witness
and the actual compact-group Haar measure's full support. -/
theorem p4Q2JE_originalWilsonHaarZeroDerivativeLp_norm_pos :
    0 < ‖p4Q2JE_originalWilsonHaarZeroDerivativeLp H‖ := by
  have h0 := p4Q2JE_originalWilsonHaarZeroDerivativeLp_ne_continuousConstant H 0
  have hConstZero :
      ContinuousMap.toLp 2 haar ℝ
        (⟨fun _ : Cfg => (0 : ℝ), continuous_const⟩ : C(Cfg, ℝ)) =
          0 := by
    change ContinuousMap.toLp 2 haar ℝ (0 : C(Cfg, ℝ)) = 0
    exact map_zero (ContinuousMap.toLp 2 haar ℝ)
  rw [hConstZero] at h0
  exact norm_pos_iff.mpr h0

end OriginalWilsonFirstVariation
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonHaarRow_hasDerivAt_zero_profile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonZeroDerivativeProfile_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonZeroDerivativeProfile_nonconstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonZeroDerivativeProfile_centralTwist_gap_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonHaarZeroDerivativeLp_ne_continuousConstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JE_originalWilsonHaarZeroDerivativeLp_norm_pos
