import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorWilsonSectionDetectionV5_KW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverTemporalCovarianceV5_JQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonKernelGramV5_KD
import Mathlib.Tactic

/-!
# P4-Q2-KX — actual physical constant-unit Wilson receiver is strictly positive
# and detected through the original interacting-posterior Wilson sections

KW proves original two-interacting-Wilson-posterior difference δ is
detectable by actual SU(2) Wilson kernel sections, also after
multiplication by a continuous receiver nonzero at identity.

Here F is NOT a synthetic test: it is JQ's authentic physical
Gauss-law receiver of the actual physical constant unit vector,
using the original Wilson transfer and the original joint Perron
square-root factor. We prove first that the true full-spatial
transfer of this unit is exactly the original one-slab Wilson
kernel mass of KB/KD, then use KD mass positivity and the genuine
Perron half-density positivity to show the receiver is positive
at EVERY SU(2) right-link insertion. KW now yields a nonzero
original Wilson one-link kernel-section test against δ times
this physical unit receiver.

The original GI expectation gap is NOT identified with this
Wilson-section convolution. Its full left-boundary half-density
factorization remains open. No independent-Haar posterior,
rank axiom, sorry, H1-C3, or continuum gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2

/-- The ORIGINAL finite-volume Wilson transfer of the genuine
physical constant unit is exactly the ORIGINAL full spatial
one-slab Wilson kernel mass used by KB/KD. No posterior is changed. -/
theorem p4Q2KX_originalPhysicalUnitTransfer_eq_originalWilsonKernelMass
    (b : ℝ) (B : Cfg) :
    decomposableOneSliceTransferIntegral H 2 b U B =
      p4Q2KB_originalSpatialWilsonKernelMass H b B := by
  have hU :
      (fun A : Cfg => (U : Lp ℝ 2 haar) A) =ᵐ[haar]
        (fun _ : Cfg => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar]
      (fun _ => 1)
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  unfold decomposableOneSliceTransferIntegral
    p4Q2KB_originalSpatialWilsonKernelMass
  apply integral_congr_ae
  filter_upwards [hU] with A hA
  rw [hA]
  ring

/-- Actual normalized physical constant-source SU(2) receiver
is the strictly positive original kernel mass divided by the
genuine positive Perron joint square-root, times the true
squared inverse transfer operator norm. -/
theorem p4Q2KX_originalPhysicalUnitReceiver_eq_originalKernelMass
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e z g =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ ^ 2 *
      p4Q2KB_originalSpatialWilsonKernelMass H b
        (Function.update z.2 e g) /
      continuousJointSqrtDensity H 2 (by norm_num) b hb
        (z.1, Function.update z.2 e g) := by
  rw [p4Q2JQ_originalPhysicalSourceLinkReceiver_apply,
    p4Q2GN_originalReceiver_eq_transferIntegral,
    p4Q2KX_originalPhysicalUnitTransfer_eq_originalWilsonKernelMass]

/-- Every value of the literal TRUE physical unit receiver is
strictly positive, at every coupling b>=0 and any actual SU(2)
right-link insertion. In particular its identity value is nonzero. -/
theorem p4Q2KX_originalPhysicalUnitReceiver_pos
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    0 < p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb U e z g := by
  rw [p4Q2KX_originalPhysicalUnitReceiver_eq_originalKernelMass]
  have hT : 0 <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖⁻¹ :=
    inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b hb)
  have hM := p4Q2KD_originalWilsonSpatialKernelMass_pos
    H b (Function.update z.2 e g)
  have hS := continuousJointSqrtDensity_pos H 2 (by norm_num)
    b hb (z.1, Function.update z.2 e g)
  exact div_pos (mul_pos (pow_pos hT 2) hM) hS

/-- The original TRUE physical constant-unit GI receiver,
multiplied by the difference of the TWO ORIGINAL interacting
Wilson conditional posteriors, is detected by an actual SU(2)
Wilson kernel section. This is a proven *physical receiver*
specialization of KW's analytic interface, not a nonzero GI
expectation gap or a second spatial Wilson context theorem. -/
theorem p4Q2KX_originalPhysicalUnitPosterior_detected_by_trueWilsonSection
    (b : ℝ) (hb : 0 < b) (e : Link) (z : Cfg × Cfg) :
    ∃ g : Gauge,
      (∫ h : Gauge, specialUnitaryWilsonRelativeKernel 2 b g h *
        (p4Q2GB_originalWilsonPosteriorLeftDensityContrast H b hb.le z.2 e h *
          p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le U e z h)
        ∂nu) ≠ 0 := by
  exact p4Q2KW_originalWeightedPosterior_detected_by_trueWilsonSection
    H b hb z.2 e
    (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb.le U e z)
    (ne_of_gt (p4Q2KX_originalPhysicalUnitReceiver_pos H b hb.le e z 1))

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KX_originalPhysicalUnitTransfer_eq_originalWilsonKernelMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KX_originalPhysicalUnitReceiver_eq_originalKernelMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KX_originalPhysicalUnitReceiver_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KX_originalPhysicalUnitPosterior_detected_by_trueWilsonSection
