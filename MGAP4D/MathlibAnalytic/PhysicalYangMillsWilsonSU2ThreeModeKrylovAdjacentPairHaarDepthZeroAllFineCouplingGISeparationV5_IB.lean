import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroPhysicalSourceGLPositivityV5_IA
import Mathlib.Tactic

/-!
# P4-Q2-IB: all-fine-beta physical separation at genuine Krylov depth zero

At physical right-Krylov depth r=0 there is only ONE signed
coefficient; the actual zero-depth source is the ORIGINAL gauge
invariant constant unit for ANY fine coupling beta(n+1)>=0.
HY proves this actual source has a NONZERO ORIGINAL two-interacting-
Wilson-posterior GI expectation gap at some genuine left boundary,
for EVERY physical link and right configuration at frozen beta(n)>0.

HG already proves that one such true anchor gives
finrank(K) <= r for the exact all-context detector common kernel K.
At r=0, mathlib's Submodule.finrank_eq_zero gives K=bot, with no
assumption beta(n+1)=0. The already-verified inclusion ker(S) <= K
then proves ker(S)=K=bot. Thus the true original Wilson GL mass
and physical residual Gram are strictly positive for EVERY nonzero
depth-zero coefficient even when the FINE coupling is positive.

For exact HK finite physical SU(2) detector sets s, the genuine GI-SOS
Gram R and the true source Haar-L² Gram Qsrc have identical ranks; the
independently defined genuine GL integral Gram B shares that rank.
The result does NOT assert source separation for r>0 at positive fine
coupling, numerical uniform bounds, H1-C3, OS Hamiltonian or the
continuum four-dimensional Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IB_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRightDepthZero

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (0 + 1) → ℝ
local notation "Context" => Link × Pair
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "GI" =>
  p4Q2HM_actualRightOriginalGIContextMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The all-context true two-Wilson-posterior GI detector kernel is
TRIVIAL in the actual one-mode Krylov family at frozen beta(n)>0,
without setting fine beta(n+1) to zero. -/
theorem p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    JointKernel = ⊥ := by
  have hOr :=
    p4Q2HY_actualRightZeroDepth_originalWilsonGI_anchor_nonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  obtain ⟨z, hAnchor⟩ : ∃ z : Pair,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e z ≠ 0 := by
    rcases hOr with h0 | h1
    · exact ⟨(originalWilsonExplicitIdentityBoundary Hn, right), h0⟩
    · exact ⟨(p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right), h1⟩
  have hBound : Module.finrank ℝ ↥JointKernel ≤ 0 :=
    p4Q2HG_actualRightGIJointKernel_finrank_le_of_anchor_ne
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 e z hAnchor
  have hZero : Module.finrank ℝ ↥JointKernel = 0 := by omega
  exact (Submodule.finrank_eq_zero).mp hZero

/-- For every nonnegative fine beta(n+1), the actual ONE-mode right
Krylov physical source synthesis and the true Wilson GI detector
are both injective. This source separation is NOT extended to r>0. -/
theorem p4Q2IB_depthZero_originalGI_jointKernel_eq_physicalSourceKernel
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    JointKernel = (PhysicalSource).ker := by
  have hBot : JointKernel = ⊥ :=
    p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hSourceLe : (PhysicalSource).ker ≤ JointKernel := by
    intro a ha
    exact p4Q2HG_actualSource_zero_mem_GIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 0 a ((LinearMap.mem_ker).mp ha)
  apply le_antisymm
  · rw [hBot]
    exact bot_le
  · exact hSourceLe

/-- The true original two-posterior Wilson GL integral mass is
strictly positive for EVERY nonzero signed depth-zero coefficient,
irrespective of fine beta(n+1)>=0. -/
theorem p4Q2IB_depthZero_originalWilsonGLMass_pos_of_coeff_ne_zero
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link)
    (a : Coeff) (ha : a ≠ 0) :
    0 < OriginalMass
      (∑ j : Fin (0 + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) := by
  have hBot : JointKernel = ⊥ :=
    p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hOutside : a ∉ JointKernel := by
    rw [hBot]
    simpa using ha
  exact p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n 0 hFrozen a hOutside

/-- The original PHYSICAL pair-Haar residual Gram is strictly
positive on the complete nonzero one-mode coefficient space
for every nonnegative fine beta; no synthetic Gram is substituted. -/
theorem p4Q2IB_depthZero_originalPhysicalGram_pos_of_coeff_ne_zero
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link)
    (a : Coeff) (ha : a ≠ 0) :
    0 < star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 0) a) := by
  have hBot : JointKernel = ⊥ :=
    p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hOutside : a ∉ JointKernel := by
    rw [hBot]
    simpa using ha
  exact p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n 0 hFrozen a hOutside

/-- Exact finite original Wilson GI SOS and physical Haar-L² source
Gram ranks agree at depth zero for ANY nonnegative fine coupling. -/
theorem p4Q2IB_depthZero_originalGIGram_rank_eq_physicalSourceGram
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link)
    (s : Finset Context) (hExact : (FiniteDetector s).ker = JointKernel) :
    (R s).rank = (Qsrc).rank := by
  have hSep : (PhysicalSource).ker = JointKernel :=
    (p4Q2IB_depthZero_originalGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e).symm
  exact (p4Q2HN_actualRight_sourceSeparation_iff_GIGram_rank_eq_sourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n 0 s hExact).mp hSep

/-- The original GL INTEGRAL Gram and the finite GI SOS Gram both have
the same rank as the distinct true physical Haar-L² source Gram for
any nonnegative fine coupling at depth zero. -/
theorem p4Q2IB_depthZero_exists_allThree_originalWilsonGram_rank_certificate
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      (B hFrozen).rank = (R s).rank ∧
      (R s).rank = (Qsrc).rank := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 0
  refine ⟨s, hs, ?_, ?_⟩
  · calc
      (B hFrozen).rank = (GI s).rank :=
        p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 0 hFrozen s hs
      _ = (R s).rank :=
        (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 0 s).symm
  · exact p4Q2IB_depthZero_originalGIGram_rank_eq_physicalSourceGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e s hs

end ActualRightDepthZero
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_originalGI_jointKernel_eq_bot
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_originalGI_jointKernel_eq_physicalSourceKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_originalWilsonGLMass_pos_of_coeff_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_originalPhysicalGram_pos_of_coeff_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_originalGIGram_rank_eq_physicalSourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IB_depthZero_exists_allThree_originalWilsonGram_rank_certificate
