import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIDetectorFineZeroFactorizationV5_HC
import Mathlib.Tactic

/-!
# P4-Q2-HD: whole-boundary original GI detector/source kernel and physical Gram

HC proved the exact fine-beta-zero factorization for the ACTUAL GI gap of
TWO original interacting Wilson posterior measures:
  Delta(F_a,e,z) = (sum_j a_j) * Delta(R_0,e,z).

First establish, independently of fine coupling, that every ACTUAL zero
physical source is GI-undetected at all links and pair boundaries.
This direction uses GN's original Wilson transfer-fiber formula, not
GU/HB's distinct two-left-response square posterior mass.

Then obtain the precise WHOLE-BOUNDARY kernel dichotomy at fine beta=0:
  [forall e,z, Delta(F_a,e,z)=0]
    iff [sum_j a_j=0 OR forall e,z, Delta(R_0,e,z)=0].

Finally under an EXPLICIT positive pair-Haar-measure GI detection
hypothesis for the actual zero-depth physical unit, prove STRICT
positivity of the genuine original fine-right Krylov Gram for any signed
coefficient vector with nonzero sum. In particular no false positive
all-coefficient frame is postulated in the rank-one fine endpoint.

No unconditional zero-depth GI anchor nonvanishing, no positive fine-beta
physical frame, no uniformity in H,n,r, H1-C3, or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 800000

local instance p4Q2HD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A zero source in the true physical gauge-invariant Hilbert space is
undetected by the ACTUAL two-original-Wilson-posterior GI expectation
gap at every physical link and every pair context. This is true at ANY
nonnegative frozen beta: no finite-volume injectivity hypothesis. -/
theorem p4Q2HD_originalPhysicalSource_zero_implies_GI_null
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (hf : f = 0)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e z = 0 := by
  apply p4Q2GN_originalTransferNull_implies_detectorNull
    H beta hbeta f
  intro B
  subst f
  change decomposableOneSliceTransferIntegral H 2 beta
    (0 : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) B = 0
  rw [p4Q2GZ_originalTransferIntegral_eq_kernelIntegral]
  simp

section ActualFineRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Unconditional source-kernel containment in GI's ACTUAL two-Wilson-
posterior detector for every actual fine beta and frozen beta. -/
theorem p4Q2HD_actualSource_zero_implies_allOriginalGI_null
    (a : Fin (r + 1) → ℝ)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0)
    (e : Link) (z : Cfg × Cfg) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
  exact p4Q2HD_originalPhysicalSource_zero_implies_GI_null
    Hn (beta n) (hbeta n) _ hSource e z

/-- The whole set of GI two-posterior contexts at fine beta=0 detects
the signed source iff the true zero-depth GI anchor is nonzero at SOME
context. Its alternative full-anchor obstruction is retained explicitly. -/
theorem p4Q2HD_fineZero_allOriginalGI_null_iff
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ) :
    (∀ e : Link, ∀ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0) ↔
      (∑ j : Fin (r + 1), a j) = 0 ∨
      (∀ e : Link, ∀ z : Cfg × Cfg,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n 0) e z = 0) := by
  constructor
  · intro hAll
    by_cases hc : (∑ j : Fin (r + 1), a j) = 0
    · exact Or.inl hc
    · right
      intro e z
      have hOr :=
        (p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r hFineZero a e z).mp (hAll e z)
      exact hOr.resolve_left hc
  · intro h e z
    have hPoint :=
      (p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFineZero a e z)
    rcases h with hc | hAnchor
    · exact hPoint.mpr (Or.inl hc)
    · exact hPoint.mpr (Or.inr (hAnchor e z))

/-- When at least one TRUE original two-Wilson posterior GI anchor is
nonzero, the kernel of the full contextual GI detector on this true
fine-beta-zero Krylov family equals the actual physical source kernel.
This avoids any unproved converse for arbitrary positive fine beta. -/
theorem p4Q2HD_fineZero_allOriginalGI_null_iff_source_zero_of_anchor_exists
    (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (hAnchor : ∃ e : Link, ∃ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0) :
    (∀ e : Link, ∀ z : Cfg × Cfg,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0) ↔
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  constructor
  · intro hAll
    obtain ⟨e, z, hAnchorNe⟩ := hAnchor
    have hOr :=
      (p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFineZero a e z).mp (hAll e z)
    have hSum : (∑ j : Fin (r + 1), a j) = 0 :=
      hOr.resolve_right hAnchorNe
    exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineZero a).mpr hSum
  · intro hSource e z
    exact p4Q2HD_actualSource_zero_implies_allOriginalGI_null
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hSource e z

/-- A TRUE non-pair-Haar-a.e.-zero GI anchor on ONE actual physical link
gives strict positivity of the ACTUAL fine-right Krylov Gram for any
rank-one fine source whose signed coefficient SUM is nonzero. This is a
correct physical-quotient Rayleigh statement, not a false positive
lower frame on all of R^(r+1). -/
theorem p4Q2HD_fineZero_Gram_pos_of_actualGI_anchor_notAE
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (a : Fin (r + 1) → ℝ)
    (hSum : (∑ j : Fin (r + 1), a j) ≠ 0)
    (e : Link)
    (hAnchor :
      ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n) (RightFactor n 0) e z = 0) :
    0 < star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) := by
  have hDetect :
      ¬ ∀ᵐ z ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure Hn 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z = 0 := by
    intro hAll
    apply hAnchor
    filter_upwards [hAll] with z hz
    have hOr :=
      (p4Q2HC_fineZero_originalGIExpectationGap_zero_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFineZero a e z).mp hz
    exact hOr.resolve_left hSum
  simpa only [fineRightKrylovPairHaarResidualGram] using
    (p4Q2GI_originalWilsonPhysicalGram_pos_of_oneLink_expectationGap_notAEZero
      Hn (beta n) hFrozen
      (fun j : Fin (r + 1) => RightFactor n (j : ℕ))
      a e hDetect)

end ActualFineRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HD_originalPhysicalSource_zero_implies_GI_null
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HD_actualSource_zero_implies_allOriginalGI_null
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HD_fineZero_allOriginalGI_null_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HD_fineZero_allOriginalGI_null_iff_source_zero_of_anchor_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HD_fineZero_Gram_pos_of_actualGI_anchor_notAE
