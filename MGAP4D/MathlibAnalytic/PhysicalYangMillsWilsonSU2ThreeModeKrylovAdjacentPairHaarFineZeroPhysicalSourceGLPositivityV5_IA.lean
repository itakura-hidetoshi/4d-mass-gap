import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroActualSourceGISeparationV5_HZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralDetectorMatrixV5_HO
import Mathlib.Tactic

/-!
# P4-Q2-IA: original Wilson source-level GL detection at fine beta zero

HY proves the original two-interacting-Wilson-posterior expectation
difference detects the actual zero-depth source. HZ thereby identifies
the full original GI common detector kernel with the ACTUAL physical
source-synthesis kernel when the fine coupling beta(n+1)=0 and the
frozen Wilson coupling beta(n)>0.

This file combines that genuine physical source separation with HI's
unconditional original Wilson spatial GL mass nullity and strict
positivity and HO's original GL integral matrix. Consequently at
the fine-beta-zero endpoint:
* original physical GL mass vanishes exactly for vanishing true source;
* GL mass is strictly positive for every nonzero actual physical source;
* the original physical pair-Haar residual Gram has positive quadratic
  value on every coefficient synthesizing a nonzero actual source;
* original GL integral Gram is strictly positive on nonzero physical
  sources and has the SAME RANK as the TRUE source Haar-L² Gram;
* an HK finite genuine SU(2) detector certificate realizes simultaneously
  the source, original GI-SOS and original GL-integral ranks.

The coefficients may be linearly dependent. These are qualitative
fixed-finite-volume statements. No numerical or H/n/r/spacing-uniform
physical source-frame coefficient, positive fine beta source separation,
H1-C3, OS Hamiltonian or continuum Yang--Mills mass gap is proved.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2IA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IA_linksFintype (H : ℕ) :
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
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "GI" =>
  p4Q2HM_actualRightOriginalGIContextMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- At genuine fine beta zero, the kernel of the original Wilson
two-interacting-posterior GL spatial integral mass equals the kernel
of the ACTUAL physical source synthesis. -/
theorem p4Q2IA_fineZero_originalWilsonGLMass_zero_iff_physicalSource_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) (a : Coeff) :
    OriginalMass
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) = 0 ↔
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 := by
  have hSep : JointKernel = (PhysicalSource).ker :=
    p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero right e
  rw [p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a, hSep]
  change (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0 ↔
    (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) = 0
  rfl

/-- Every genuinely NONZERO fine-beta-zero physical source has a
STRICTLY POSITIVE original Wilson spatial GL mass. Not an assumed
physical source frame or a positive bound uniform in lattice volume. -/
theorem p4Q2IA_fineZero_originalWilsonGLMass_pos_of_physicalSource_ne_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) (a : Coeff)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0) :
    0 < OriginalMass
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) := by
  have hSep : JointKernel = (PhysicalSource).ker :=
    p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero right e
  have hNot : a ∉ JointKernel := by
    rw [hSep]
    intro ha
    exact hSource ((LinearMap.mem_ker).mp ha)
  exact p4Q2HI_actualRightGLMass_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a hNot

/-- Physical-source detection yields strict positivity of the
TRUE original pair-Haar residual Gram at the fine-beta-zero endpoint,
not merely of the GI finite detector or the GL integral Gram. -/
theorem p4Q2IA_fineZero_originalPhysicalGram_pos_of_source_ne_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) (a : Coeff)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0) :
    0 < star a ⬝ᵥ
      (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) := by
  have hSep : JointKernel = (PhysicalSource).ker :=
    p4Q2HZ_fineZero_actualRightGI_jointKernel_eq_physicalSourceKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero right e
  have hNot : a ∉ JointKernel := by
    rw [hSep]
    intro ha
    exact hSource ((LinearMap.mem_ker).mp ha)
  exact p4Q2HI_actualRightGram_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a hNot

/-- The original GL INTEGRAL detector Gram has positive Rayleigh
value for every nonzero actual physical source at fine beta zero. -/
theorem p4Q2IA_fineZero_originalGLIntegralGram_pos_of_source_ne_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) (a : Coeff)
    (hSource :
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ)) ≠ 0) :
    0 < star a ⬝ᵥ ((B hFrozen) *ᵥ a) := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a]
  exact p4Q2IA_fineZero_originalWilsonGLMass_pos_of_physicalSource_ne_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen hFineZero right e a hSource

/-- At the true fine-beta-zero endpoint, original Wilson GL integral
Gram, finite exact Wilson GI-SOS Gram and the DISTINCT physical Haar-L²
source Gram have identical ranks. No actual Gram matrices are equated. -/
theorem p4Q2IA_fineZero_originalGLIntegralGram_rank_eq_physicalSourceGram
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (B hFrozen).rank = (Qsrc).rank := by
  calc
    (B hFrozen).rank = (GI s).rank :=
      p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen s hExact
    _ = (R s).rank :=
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).symm
    _ = (Qsrc).rank :=
      p4Q2HZ_fineZero_actualRight_originalGIGram_rank_eq_physicalSourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen hFineZero right e s hExact

/-- Choose one EXACT finite true SU(2) physical-context certificate
that simultaneously identifies all three original Wilson detector and
physical source Gram ranks at the genuine fine-beta-zero endpoint. -/
theorem p4Q2IA_fineZero_exists_originalWilson_allThreeGram_sourceRank_certificate
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (right : Cfg) (e : Link) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      (B hFrozen).rank = (R s).rank ∧
      (R s).rank = (Qsrc).rank := by
  obtain ⟨s, hs, hRank⟩ :=
    p4Q2HZ_fineZero_exists_originalWilsonGIGram_sourceRank_certificate
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen hFineZero right e
  refine ⟨s, hs, ?_, hRank⟩
  calc
    (B hFrozen).rank = (GI s).rank :=
      p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen s hs
    _ = (R s).rank :=
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).symm

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_originalWilsonGLMass_zero_iff_physicalSource_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_originalWilsonGLMass_pos_of_physicalSource_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_originalPhysicalGram_pos_of_source_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_originalGLIntegralGram_pos_of_source_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_originalGLIntegralGram_rank_eq_physicalSourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IA_fineZero_exists_originalWilson_allThreeGram_sourceRank_certificate
