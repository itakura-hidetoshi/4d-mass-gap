import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualZeroModeOriginalGIAnchorV5_HY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIFiniteSumSquaresDetectionGramV5_HN
import Mathlib.Tactic

/-!
# P4-Q2-HZ: true original Wilson physical-source separation at fine beta=0

HY establishes that at positive frozen beta(n) the ACTUAL fine-right
zero-depth Krylov physical source is detected by one of the TWO
original interacting Wilson posterior GI left contexts, at every
physical spatial link and every right boundary.

The older conditional HG/HD source-kernel theorem is thus made
unconditional for the GENUINE fine-beta(n+1)=0 right-Krylov family.
For this endpoint the modes coincide with the same physical unit;
their signed source is exactly sum(coefficients)*unit, and the genuine
all-context GI common kernel equals the physical-source synthesis
kernel even for arbitrary Krylov depth and dependent source modes.

HM/HN then give EQUALITY of the ranks of the actual physical
Haar-L² source Gram and the genuine finite SU(2) GI SOS Gram on
every HK exact finite context certificate. Existence of a suitable
finite physical certificate follows from HK.

This does NOT prove physical separation at positive fine coupling,
volume/spacing/depth-uniform quantitative source bounds, H1-C3,
OS Hamiltonian, or a continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HZ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Pair" => Cfg × Cfg
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "Context" => Link × Pair
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Source" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Physical source separation is now unconditional at the authentic
fine-beta-zero endpoint for every finite n,r and every positive frozen
Wilson coupling. No independent source modes are assumed. -/
theorem p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) :
    JointKernel = Source.ker := by
  have hOr :=
    p4Q2HY_actualRightZeroDepth_originalWilsonGI_anchor_nonzero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen right e
  have hAnchor : ∃ e' : Link, ∃ z : Pair,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        Hn (beta n) (hbeta n) (RightFactor n 0) e' z ≠ 0 := by
    rcases hOr with h0 | h1
    · exact ⟨e, (originalWilsonExplicitIdentityBoundary Hn, right), h0⟩
    · exact ⟨e, (p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right), h1⟩
  apply Submodule.ext
  intro a
  change a ∈ JointKernel ↔
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0
  exact p4Q2HG_fineZero_GIJointKernel_mem_iff_physicalSource_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFineZero hAnchor a

/-- Every HK exact genuine SU(2) physical detector certificate has
the SAME rank as the TRUE physical Haar-L² Krylov source Gram at the
actual fine-beta-zero endpoint. This is not an H-uniform frame. -/
theorem p4Q2HZ_fineZero_actualRight_originalGIGram_rank_eq_physicalSourceGram
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link)
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (R s).rank = Qsrc.rank := by
  have hSep :
      Source.ker = JointKernel :=
    (p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero right e).symm
  exact (p4Q2HN_actualRight_sourceSeparation_iff_GIGram_rank_eq_sourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact).mp hSep

/-- Choose actual finite original Wilson physical contexts whose
finite GI Gram has exactly the real physical source Gram rank
at every fine-beta-zero finite Krylov depth. -/
theorem p4Q2HZ_fineZero_exists_originalWilsonGIGram_sourceRank_certificate
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      (R s).rank = Qsrc.rank := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  exact p4Q2HZ_fineZero_actualRight_originalGIGram_rank_eq_physicalSourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen hFineZero right e s hs

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HZ_fineZero_actualRight_originalGIGram_rank_eq_physicalSourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HZ_fineZero_exists_originalWilsonGIGram_sourceRank_certificate
