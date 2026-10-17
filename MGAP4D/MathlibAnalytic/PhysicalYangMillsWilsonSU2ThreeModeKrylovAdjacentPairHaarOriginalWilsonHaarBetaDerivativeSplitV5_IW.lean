import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonHaarBetaDerivativeV5_IW
import Mathlib.Tactic

/-!
# P4-Q2-IW: explicit physical-Haar beta-zero Wilson derivative decomposition

The first-order response of the true SU(2) Wilson Haar row separates into
half of the actual right spatial Wilson action, half the left spatial Haar
mean, and the actual temporal crossing-action Haar mean. This is a
literal original-Wilson statement: neither conditional GI posteriors nor
an artificial independent replacement are introduced.

The temporal-crossing Haar mean being independent of the right boundary
and spatial plaquette energy nonconstancy are separate next proof obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section
set_option maxHeartbeats 2600000

local instance p4Q2IWSplit_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IWSplit_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IWSplit_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IWSplit_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IWSplit_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualWilsonSplit

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2

/-- Literal finite physical-Haar mean of the complete original one-slab
action is a sum of the left spatial mean, the true temporal crossing mean,
and the right spatial half-action. -/
theorem p4Q2IW_originalWilsonOneSlabHaarAction_mean_split
    (B : Cfg) :
    (∫ A : Cfg, S A B ∂haar) =
      (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) +
        (∫ A : Cfg, C A B ∂haar) +
        (1 / 2 : ℝ) * W B := by
  have hWInt : Integrable (fun A : Cfg => W A) haar :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
      H 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPair : Continuous (fun A : Cfg => (A, B)) :=
    continuous_id.prodMk continuous_const
  have hCcont : Continuous (fun A : Cfg => C A B) := by
    have h := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using h
  have hCInt : Integrable (fun A : Cfg => C A B) haar :=
    hCcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHalfInt : Integrable (fun A : Cfg => (1 / 2 : ℝ) * W A) haar :=
    hWInt.const_mul _
  change (∫ A : Cfg, (1 / 2 : ℝ) * W A + C A B +
      (1 / 2 : ℝ) * W B ∂haar) = _
  rw [integral_add (hHalfInt.add hCInt) (integrable_const _)]
  rw [integral_add hHalfInt hCInt]
  rw [integral_const_mul]
  simp

/-- The sought explicit beta=0 first-order formula for the literal original
SU(2) Wilson Haar row, including BOTH spatial Wilson half-actions and the
temporal crossing term. No assumption of right-boundary nonconstancy occurs. -/
theorem p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero_explicit
    (B : Cfg) :
    HasDerivAt
      (fun beta : ℝ => p4Q2IV_originalWilsonUnitHaarKernelSection H beta B)
      (-(1 / 2 : ℝ) * W B -
        (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) -
        (∫ A : Cfg, C A B ∂haar))
      0 := by
  have hSplit := p4Q2IW_originalWilsonOneSlabHaarAction_mean_split H B
  have hDeriv := p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero H B
  have hRewrite :
      -(∫ A : Cfg, S A B ∂haar) =
        -(1 / 2 : ℝ) * W B -
          (1 / 2 : ℝ) * (∫ A : Cfg, W A ∂haar) -
          (∫ A : Cfg, C A B ∂haar) := by
    rw [hSplit]
    ring
  exact hRewrite ▸ hDeriv

end ActualWilsonSplit
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonOneSlabHaarAction_mean_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero_explicit
