import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarDepthZeroAllFineCouplingGISeparationV5_IB
import Mathlib.Tactic

/-!
# P4-Q2-ID: open physical GI/GL detection region at ALL fine couplings and depths

HY proves the original two-interacting-Wilson-posterior GI expectation
gap of the TRUE fine-right zero-depth physical source is nonzero at
one of the literal identity/pi left boundaries for every physical
SU(2) spatial link and right configuration when frozen beta(n)>0.
GX proves this genuine zero-mode source equals the signed physical
Krylov synthesis of the canonical depth-r zero-selector coefficient
for EVERY finite r and EVERY nonnegative fine beta(n+1).

HF proves the genuine original GI expectation gap is a real linear
functional of the actual fine-right coefficient, and that its
nonzero-detection locus is OPEN in the real coefficient topology.
Hence the HY true original GI anchor has a nonempty open metric ball
of coefficient perturbations in which the SAME true Wilson context
still has NONZERO genuine two-posterior GI expectation difference.

Using HG/HI, EVERY coefficient in this open ball has a nonzero
ACTUAL physical Haar-L² source, a strictly positive ORIGINAL Wilson
pair-Haar spatial GL gap-square mass, and a strictly positive true
physical pair-Haar residual Gram quadratic value. There is no
independent-Haar conditional or fictitious source frame.

This extends guaranteed original physical detection to a genuine
OPEN family of signed higher-depth Krylov combinations at ANY fine
beta(n+1)>=0, including positive beta(n+1). The local radius may
depend on the physical volume, scale, n, r, link, right background,
posterior rows and frozen beta. It does NOT assert full source
separation for all signed coefficients or a continuum 4D mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2ID_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2ID_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2ID_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2ID_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2ID_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2ID_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualArbitraryDepth

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Modal" =>
  p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- A single ACTUAL original Wilson GI context detects the canonical
zero-mode coefficient for every finite Krylov depth and ANY fine beta.
The context is one of two literal true Wilson left boundary choices. -/
theorem p4Q2ID_actualRight_everyDepth_trueGI_anchor_at_zeroCoefficient
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ z : Pair,
      Modal e z (p4Q2GX_rightZeroCoefficient r) ≠ 0 := by
  have hOr :=
    p4Q2HY_actualRightZeroDepth_originalWilsonGI_anchor_nonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  obtain ⟨z, hz⟩ : ∃ z : Pair,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0 := by
    rcases hOr with hId | hPi
    · exact ⟨(originalWilsonExplicitIdentityBoundary Hn, right), hId⟩
    · exact ⟨(p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right), hPi⟩
  refine ⟨z, ?_⟩
  change p4Q2HF_actualRightGIModalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e z (p4Q2GX_rightZeroCoefficient r) ≠ 0
  rw [← p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r (p4Q2GX_rightZeroCoefficient r) e z]
  rw [p4Q2GX_actualRightCoefficientSource_eq_zeroMode
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r]
  exact hz

/-- At arbitrary depth and arbitrary nonnegative fine coupling there
is an ACTUAL positive-radius neighborhood of genuine signed Krylov
coefficients around the physical unit selector, on which the true
two-Wilson-posterior GI gap, original spatial GL mass and physical
residual Gram remain strictly nonzero/positive. The radius is
model-dependent; no all-coefficient source frame is inferred. -/
theorem p4Q2ID_actualRight_exists_open_ball_trueGI_GL_and_physical_detected
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ (z : Pair) (epsilon : ℝ), 0 < epsilon ∧
      ∀ a : Coeff,
        dist a (p4Q2GX_rightZeroCoefficient r) < epsilon →
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z ≠ 0 ∧
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0 ∧
          0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          0 < star a ⬝ᵥ
            (Matrix.mulVec
              (fineRightKrylovPairHaarResidualGram
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r) a) := by
  obtain ⟨z, hAnchor⟩ :=
    p4Q2ID_actualRight_everyDepth_trueGI_anchor_at_zeroCoefficient
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen right e
  have hOpen : IsOpen {a : Coeff | Modal e z a ≠ 0} :=
    p4Q2HF_actualRightGI_detected_isOpen
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z
  obtain ⟨epsilon, hepsilon, hBall⟩ :=
    (Metric.isOpen_iff.mp hOpen)
      (p4Q2GX_rightZeroCoefficient r) hAnchor
  refine ⟨z, epsilon, hepsilon, ?_⟩
  intro a ha
  have hNearby : a ∈ Metric.ball (p4Q2GX_rightZeroCoefficient r) epsilon :=
    Metric.mem_ball.mpr (by simpa only [dist_comm] using ha)
  have hModal : Modal e z a ≠ 0 := hBall hNearby
  have hGI :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) e z ≠ 0 := by
    rw [p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z]
    exact hModal
  have hOutside : a ∉ JointKernel := by
    intro hK
    have hAll :=
      (p4Q2HG_actualRightGIJointModalKernel_mem_iff
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a).mp hK
    exact hGI (hAll e z)
  have hSourceNe :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0 := by
    intro hSource
    exact hOutside
      (p4Q2HG_actualSource_zero_mem_GIJointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a hSource)
  have hGL :
      0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) :=
    p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a hOutside
  have hGram :
      0 < star a ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) a) :=
    p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a hOutside
  exact ⟨hGI, hSourceNe, hGL, hGram⟩

end ActualArbitraryDepth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ID_actualRight_everyDepth_trueGI_anchor_at_zeroCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ID_actualRight_exists_open_ball_trueGI_GL_and_physical_detected
