import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverLeftBoundaryExplicitSlopeV5_PZ37AEU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEV — true centered physical right-boundary Wilson transfer variation

AEU removed the left-receiver hypothesis. This append-only module
now transfers AEM's proved ORIGINAL kernel chordal slope 13*beta0
to the signed, ORIGINAL ZW centered Gauss-law source via its exact
one-slab Haar transfer integral. No positive-source substitution,
altered action, new posterior, finite-net certificate or source
regularization hypothesis is introduced.

The relevant finite-volume source mass is its genuine Haar L1 mass.
The remaining receiver quotient factor uses AEQ and AEK.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Absolute transfer-kernel oscillation against a SIGNED Haar
source. Positivity of the source is not assumed: the original
absolute source appears under the same measure and integral. -/
theorem p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f u v : α → ℝ) (C : ℝ)
    (hf : Integrable f μ)
    (hu : Integrable (fun x => f x * u x) μ)
    (hv : Integrable (fun x => f x * v x) μ)
    (huv : ∀ x, |u x - v x| ≤ C) :
    |(∫ x, f x * u x ∂μ) - (∫ x, f x * v x ∂μ)| ≤
      C * (∫ x, |f x| ∂μ) := by
  have hfAbs : Integrable (fun x => |f x|) μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hpoint (x : α) :
      |f x * u x - f x * v x| ≤ C * |f x| := by
    have hEq : f x * u x - f x * v x = f x * (u x - v x) := by ring
    rw [hEq, abs_mul]
    calc
      |f x| * |u x - v x| ≤ |f x| * C :=
        mul_le_mul_of_nonneg_left (huv x) (abs_nonneg _)
      _ = C * |f x| := by ring
  have hI1 :
      (∫ x, f x * u x ∂μ) ≤
        (∫ x, f x * v x ∂μ) + C * (∫ x, |f x| ∂μ) := by
    calc
      (∫ x, f x * u x ∂μ) ≤
          ∫ x, (f x * v x + C * |f x|) ∂μ := by
        apply integral_mono_ae hu (hv.add (hfAbs.const_mul C))
        filter_upwards with x
        have hp := (abs_le.mp (hpoint x)).2
        change f x * u x ≤ f x * v x + C * |f x|
        linarith only [hp]
      _ = (∫ x, f x * v x ∂μ) + C * (∫ x, |f x| ∂μ) := by
        rw [integral_add hv (hfAbs.const_mul C), integral_const_mul]
  have hI2 :
      (∫ x, f x * v x ∂μ) ≤
        (∫ x, f x * u x ∂μ) + C * (∫ x, |f x| ∂μ) := by
    calc
      (∫ x, f x * v x ∂μ) ≤
          ∫ x, (f x * u x + C * |f x|) ∂μ := by
        apply integral_mono_ae hv (hu.add (hfAbs.const_mul C))
        filter_upwards with x
        have hp := (abs_le.mp (hpoint x)).1
        change f x * v x ≤ f x * u x + C * |f x|
        linarith only [hp]
      _ = (∫ x, f x * u x ∂μ) + C * (∫ x, |f x| ∂μ) := by
        rw [integral_add hu (hfAbs.const_mul C), integral_const_mul]
  apply abs_le.mpr
  constructor <;> linarith only [hI1, hI2]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local instance p4Q2PZ37AEV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0

local instance p4Q2PZ37AEV_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEV_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The actual centered physical L2 source has a finite, nonnegative
Haar L1 mass. This is the source itself, NOT a surrogate uniform source. -/
noncomputable def p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass : ℝ :=
  ∫ A : Cfg, |(f0 : Lp ℝ 2 muH) A| ∂muH

local notation "Msrc" =>
  p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H

theorem p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg :
    0 ≤ Msrc := by
  unfold p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass
  exact integral_nonneg (fun A => abs_nonneg _)

/-- EXACT original source transfer is the actual (signed) Haar
integral of the original Wilson kernel against the ZW physical
Gauss-law-centered vector. -/
theorem p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral
    (B : Cfg) :
    t B = ∫ A : Cfg,
        (f0 : Lp ℝ 2 muH) A * K A B ∂muH := by
  change (∫ A : Cfg,
      K A B * (f0 : Lp ℝ 2 muH) A ∂muH) = _
  congr 1
  funext A
  ring

/-- No external regularity assumption: integrate the PROVED AEM
13*beta0 kernel Lipschitz theorem against the unchanged signed
ZW Gauss-law source. The source amplitude is its genuine Haar L1
mass, finite because the genuine source belongs to physical L2. -/
theorem p4Q2PZ37AEV_originalCenteredTransfer_rightOneLinkChordSlope
    (B : Cfg) (i : Link) (g h : G) :
    |t (Function.update B i g) - t (Function.update B i h)| ≤
      ((13*b0)*Msrc)*dJ g h := by
  let f : Cfg → ℝ := fun A => (f0 : Lp ℝ 2 muH) A
  have hf : Integrable f muH := by
    exact (Lp.memLp (f0 : Lp ℝ 2 muH)).integrable (by norm_num)
  have hInt (D : Cfg) :
      Integrable (fun A : Cfg => f A * K A D) muH := by
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
      H 2 (by norm_num) b0 hb0 (f0 : Lp ℝ 2 muH) D
  have hK (A : Cfg) :
      |K A (Function.update B i g) -
        K A (Function.update B i h)| ≤ (13*b0)*dJ g h := by
    exact p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
      H A B i g h
  have hBound :=
    p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
      muH f (fun A : Cfg => K A (Function.update B i g))
      (fun A : Cfg => K A (Function.update B i h))
      ((13*b0)*dJ g h) hf
      (hInt (Function.update B i g))
      (hInt (Function.update B i h)) hK
  calc
    |t (Function.update B i g) - t (Function.update B i h)| =
        |(∫ A : Cfg, f A * K A (Function.update B i g) ∂muH) -
          (∫ A : Cfg, f A * K A (Function.update B i h) ∂muH)| := by
        rw [p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral,
          p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral]
    _ ≤ ((13*b0)*dJ g h)*(∫ A : Cfg, |f A| ∂muH) := hBound
    _ = ((13*b0)*Msrc)*dJ g h := by
      change ((13*b0)*dJ g h)*Msrc = ((13*b0)*Msrc)*dJ g h
      ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalCenteredTransfer_eq_originalKernelIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalCenteredTransfer_rightOneLinkChordSlope
