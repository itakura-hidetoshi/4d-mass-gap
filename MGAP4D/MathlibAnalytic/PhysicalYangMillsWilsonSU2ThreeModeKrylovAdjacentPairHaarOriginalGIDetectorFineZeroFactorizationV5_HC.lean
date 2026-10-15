import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualFineZeroPosteriorMassKernelV5_HB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferFiberDetectorKernelV5_GN
import Mathlib.Tactic

/-!
# P4-Q2-HC: exact original two-Wilson-posterior GI detector at fine beta zero

The original signed source-dependent FF response is a function of the ORIGINAL
Wilson transfer integrals, by GN. At fine beta(n+1)=0 the genuine physical
right-Krylov source is rank one: HA/GZ already factor its original frozen
transfer by the sum of signed coefficients. Transport that SAME scalar
factor, first through GN's complete signed response (with its true output
update/drift), then through the two distinct interacting original Wilson
conditional expectations in GI. The posterior laws are fixed by the frozen
beta(n), not replaced by independent Haar.

For a fixed link/context:
  Delta(F_a) = (sum_j a_j) * Delta(R_0).

Consequently the exact GI detector null criterion is
  Delta(F_a) = 0 iff sum_j a_j = 0 OR Delta(R_0) = 0.

Unlike the strict positivity of the DIFFERENT two-LEFT-response squared
posterior mass in HB, nothing here claims Delta(R_0) is nonzero. The
anchor's genuine source-specific GI nonvanishing is explicitly isolated
as the next obstruction, not silently assumed.

No positive-fine-beta signed source frame, no GI/GU mass identification,
no uniformity in volume/depth/scale, H1-C3 or continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2700000
set_option synthInstance.maxHeartbeats 800000

local instance p4Q2HC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The difference of expectations under TWO FIXED probability laws is
linear under scalar multiples of the same integrand. Unlike GU this is a
difference of two true posterior expectations, not a two-response RMS. -/
private theorem p4Q2HC_twoMeasureExpectationDifference_smul
    {α : Type*} [MeasurableSpace α]
    (μ₀ μ₁ : Measure α)
    (f g : α → ℝ) (c : ℝ)
    (hfg : ∀ x, f x = c * g x) :
    (∫ x, f x ∂μ₀) - (∫ x, f x ∂μ₁) =
      c * ((∫ x, g x ∂μ₀) - (∫ x, g x ∂μ₁)) := by
  have h₀ : (∫ x, f x ∂μ₀) = c * (∫ x, g x ∂μ₀) := by
    calc
      (∫ x, f x ∂μ₀) = ∫ x, c * g x ∂μ₀ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hfg x
      _ = c * (∫ x, g x ∂μ₀) := integral_const_mul c g
  have h₁ : (∫ x, f x ∂μ₁) = c * (∫ x, g x ∂μ₁) := by
    calc
      (∫ x, f x ∂μ₁) = ∫ x, c * g x ∂μ₁ := by
        apply integral_congr_ae
        filter_upwards with x
        exact hfg x
      _ = c * (∫ x, g x ∂μ₁) := integral_const_mul c g
  rw [h₀, h₁]
  ring

section ActualFineZero

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Genuine original frozen Wilson transfer is homogeneous in the signed
fine-right Krylov coefficient SUM at actual fine beta zero, for EVERY
physical right boundary B; this is NOT the GI expectation gap. -/
theorem p4Q2HC_fineZero_originalTransfer_eq_sum_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) (B : Cfg) :
    decomposableOneSliceTransferIntegral Hn 2 (beta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) B =
      (∑ j : Fin (r + 1), a j) *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n 0) B := by
  exact (p4Q2GZ_actualSignedRightTransfer_eq_originalModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a B).trans
    (p4Q2HA_fineZero_originalModal_eq_sum_mul
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a B)

/-- The ACTUAL original signed FF response itself factors by the
coefficient sum, with both transfer values and the full output-update
term retained. The proof uses GN's literal Wilson transfer formula. -/
theorem p4Q2HC_fineZero_originalSignedResponse_eq_sum_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      Hn 2 (by norm_num) (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e (z,g) =
      (∑ j : Fin (r + 1), a j) *
        p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
          Hn 2 (by norm_num) (beta n) (hbeta n)
          (RightFactor n 0) e (z,g) := by
  rw [p4Q2GN_originalSignedResponse_eq_transferDifference
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z g,
      p4Q2GN_originalSignedResponse_eq_transferDifference
        Hn (beta n) (hbeta n) (RightFactor n 0) e z g]
  have hT (B : Cfg) :
      decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (↑(∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)) B =
      (∑ j : Fin (r + 1), a j) *
        decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (RightFactor n 0) B := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      (p4Q2HC_fineZero_originalTransfer_eq_sum_mul
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFineZero a B)
  rw [hT z.2, hT (Function.update z.2 e g)]
  ring

/-- For EVERY genuine original pair context, the SAME two real interacting
Wilson posteriors detect the signed rank-one fine source through precisely
the sum of its coefficients times the genuine zero-depth GI anchor. -/
theorem p4Q2HC_fineZero_originalGIExpectationGap_eq_sum_mul
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z =
      (∑ j : Fin (r + 1), a j) *
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n 0) e z := by
  let F : Phys := ∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)
  let u : Phys := RightFactor n 0
  let c : ℝ := ∑ j : Fin (r + 1), a j
  let ν₀ : Measure Gauge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      Hn 2 (by norm_num) (beta n) (hbeta n)
      (originalWilsonExplicitIdentityBoundary Hn) z.2 e
  let ν₁ : Measure Gauge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
      Hn 2 (by norm_num) (beta n) (hbeta n)
      (p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e) z.2 e
  have hR (g : Gauge) :
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n) F e (z,g) =
      c * p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        Hn 2 (by norm_num) (beta n) (hbeta n) u e (z,g) := by
    exact p4Q2HC_fineZero_originalSignedResponse_eq_sum_mul
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a e z g
  change
    (∫ g, p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
       Hn 2 (by norm_num) (beta n) (hbeta n) F e (z,g) ∂ν₀) -
    (∫ g, p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
       Hn 2 (by norm_num) (beta n) (hbeta n) F e (z,g) ∂ν₁) =
      c *
        ((∫ g, p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
          Hn 2 (by norm_num) (beta n) (hbeta n) u e (z,g) ∂ν₀) -
         (∫ g, p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
          Hn 2 (by norm_num) (beta n) (hbeta n) u e (z,g) ∂ν₁))
  exact p4Q2HC_twoMeasureExpectationDifference_smul ν₀ ν₁
    (fun g => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      Hn 2 (by norm_num) (beta n) (hbeta n) F e (z,g))
    (fun g => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      Hn 2 (by norm_num) (beta n) (hbeta n) u e (z,g))
    c hR

/-- Precise ZERO-LOCUS of the true original TWO-WILSON-posterior
expectation-gap at any physical link and pair background at fine beta=0.
The second alternative is the unproved *physical GI anchor obstruction*. -/
theorem p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 ↔
      (∑ j : Fin (r + 1), a j) = 0 ∨
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z = 0 := by
  rw [p4Q2HC_fineZero_originalGIExpectationGap_eq_sum_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a e z]
  exact mul_eq_zero

/-- At any physical link/context where the true GI zero-depth anchor is
actually nonzero, detector-null is exactly physical source-null. This
anchor nonvanishing is EXPLICITLY assumed, not inferred from GU/HB RMS. -/
theorem p4Q2HC_fineZero_originalGIExpectationGap_zero_iff_source_zero_of_anchor_ne
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (e : Link) (z : Cfg × Cfg)
    (hAnchor :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 ↔
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  rw [p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a e z]
  rw [or_iff_left hAnchor]
  exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero a).symm

end ActualFineZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HC_fineZero_originalTransfer_eq_sum_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HC_fineZero_originalSignedResponse_eq_sum_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HC_fineZero_originalGIExpectationGap_eq_sum_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HC_fineZero_originalGIExpectationGap_zero_iff_source_zero_of_anchor_ne
