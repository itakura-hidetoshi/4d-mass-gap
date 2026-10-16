import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIFiniteSumSquaresDetectionGramV5_HN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralDetectorMatrixV5_HO
import Mathlib.Tactic

/-!
# P4-Q2-HP: exact original GL integral / finite Wilson GI SOS equivalence

This module compares THREE distinct actual physical matrices, without
equating them: the original integrated GL detector B, HK's exact finite
two-interacting-Wilson-posterior squared detector R=MᵀM, and the genuine
physical Haar-L² source Gram Qsrc.

For frozen beta(n)>0 and any nonnegative, independent fine beta(n+1),
the REAL integral B and finite SOS R have identical kernels and ranks
on every HK exact physical context certificate. Their genuine quadratic
zero loci and strict positive detection loci agree. Their common
kernel is the ALL-context Wilson GI kernel, not automatically ker S.

The original GL mass is strictly positive exactly for coefficients
outside that detection kernel. Rank loss against the true physical
source Gram is equivalent to an invisible NONZERO physical source.
The GL bilinear pairing annihilates every detected-null coefficient.

No finite-frame numerical constant, volume/spacing/depth uniformity,
unconditional physical-source separation, H1-C3 reconstruction,
Hamiltonian or continuum Yang-Mills mass gap is established.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HP_linksFintype (H : ℕ) :
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
local notation "Context" => Link × Pair
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
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
local notation "R" =>
  p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "GLForm" =>
  p4Q2HO_actualRightOriginalGLBilinear
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r

/-- Both fully authentic Wilson detector Gram matrices descend through
the SAME all-context GI nullspace at each HK exact finite certificate.
This does not imply equality with the Haar-L² physical synthesis kernel. -/
theorem p4Q2HP_actualRight_originalGLGram_ker_eq_finiteSOSGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (B hFrozen).mulVecLin.ker = (R s).mulVecLin.ker := by
  calc
    (B hFrozen).mulVecLin.ker = JointKernel :=
      p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen
    _ = (R s).mulVecLin.ker :=
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_ker_eq_jointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s hExact).symm

/-- The integrated Wilson detector and exactly sampled finite GI detector
have the SAME rank; this number may still be smaller than rank Qsrc. -/
theorem p4Q2HP_actualRight_originalGLGram_rank_eq_finiteSOSGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (B hFrozen).rank = (R s).rank := by
  calc
    (B hFrozen).rank = (GI s).rank :=
      p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen s hExact
    _ = (R s).rank :=
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).symm

/-- The authentic GL outer Haar integral and a finite genuine SU(2)
two-posterior GI sum of squares have EXACTLY the same zero coefficients. -/
theorem p4Q2HP_actualRight_originalGLGram_quad_zero_iff_finiteSOSGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) (a : Coeff) :
    star a ⬝ᵥ ((B hFrozen) *ᵥ a) = 0 ↔
      star a ⬝ᵥ ((R s) *ᵥ a) = 0 := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass]
  exact (p4Q2HN_actualRight_GIGram_quad_zero_iff_originalGLMass_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact hFrozen a).symm

/-- Both detector energies are nonnegative, and one is strictly positive
exactly when the other is. This is a statement about positivity loci,
not a volume-independent numerical bound between the two energies. -/
theorem p4Q2HP_actualRight_originalGLGram_quad_pos_iff_finiteSOSGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) (a : Coeff) :
    0 < star a ⬝ᵥ ((B hFrozen) *ᵥ a) ↔
      0 < star a ⬝ᵥ ((R s) *ᵥ a) := by
  have hBNonneg : 0 ≤ star a ⬝ᵥ ((B hFrozen) *ᵥ a) :=
    (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).dotProduct_mulVec_nonneg a
  have hRNonneg : 0 ≤ star a ⬝ᵥ ((R s) *ᵥ a) :=
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).dotProduct_mulVec_nonneg a
  have hZero := p4Q2HP_actualRight_originalGLGram_quad_zero_iff_finiteSOSGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen s hExact a
  constructor
  · intro hPositive
    have hNotZero : star a ⬝ᵥ ((R s) *ᵥ a) ≠ 0 := by
      intro hz
      exact (ne_of_gt hPositive) (hZero.mpr hz)
    exact lt_of_le_of_ne hRNonneg (Ne.symm hNotZero)
  · intro hPositive
    have hNotZero : star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≠ 0 := by
      intro hz
      exact (ne_of_gt hPositive) (hZero.mp hz)
    exact lt_of_le_of_ne hBNonneg (Ne.symm hNotZero)

/-- Authentic original GL detection mass is strictly positive precisely
outside the physical all-link/all-boundary GI joint coefficient kernel.
No physical synthesis injectivity or universal gap is inferred. -/
theorem p4Q2HP_actualRight_originalGLMass_pos_iff_not_mem_jointKernel
    (hFrozen : 0 < beta n) (a : Coeff) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      (Finset.univ : Finset Link) ↔ a ∉ JointKernel := by
  have hNonneg :
      0 ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) := by
    rw [← p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a]
    exact (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).dotProduct_mulVec_nonneg a
  have hZero := p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a
  constructor
  · intro hPositive hK
    exact (ne_of_gt hPositive) (hZero.mpr hK)
  · intro hNot
    have hNe : p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) ≠ 0 := by
      intro hz
      exact hNot (hZero.mp hz)
    exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- GL detection is bounded in rank by the true Haar-L² physical source
Gram. The inequality may be strict, including if fine modes depend. -/
theorem p4Q2HP_actualRight_originalGLGram_rank_le_physicalSourceGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (B hFrozen).rank ≤ (Qsrc).rank := by
  calc
    (B hFrozen).rank = (GI s).rank :=
      p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen s hExact
    _ ≤ (Qsrc).rank :=
      p4Q2HM_actualRight_originalGIMatrix_rank_le_physicalSourceGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s hExact

/-- Source separation is precisely equality of the actual GL detector
rank and the actual physical Haar-L² source Gram rank. The equality
remains an open original-Wilson analytic input in general. -/
theorem p4Q2HP_actualRight_sourceSeparation_iff_originalGLGram_rank_eq_sourceGram
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (PhysicalSource).ker = JointKernel ↔
      (B hFrozen).rank = (Qsrc).rank := by
  calc
    (PhysicalSource).ker = JointKernel ↔
        (Qsrc).rank = (GI s).rank :=
      p4Q2HM_actualRight_sourceSeparation_iff_originalGI_matrixRanksEq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s hExact
    _ ↔ (B hFrozen).rank = (Qsrc).rank := by
      rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen s hExact]
      exact eq_comm

/-- An exact physical GL Gram rank loss means a NONZERO synthesized
gauge-invariant physical source that no original finite GI detector sees.
This equivalence does NOT assert that such a source exists. -/
theorem p4Q2HP_actualRight_originalGLGram_rankLoss_iff_invisiblePhysicalSource
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    ((B hFrozen).rank < (Qsrc).rank) ↔
      ∃ a : Coeff, PhysicalSource a ≠ 0 ∧ FiniteDetector s a = 0 := by
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_rank_eq_finiteGI
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen s hExact]
  exact p4Q2HM_actualRight_originalGIMatrix_rankLoss_iff_invisiblePhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact

/-- The REAL original GL bilinear form annihilates every invisible GI
coefficient in E, in BOTH inputs. This prepares a bilinear descent to
the quotient E / JointKernel without assuming physical-source separation. -/
theorem p4Q2HP_actualRight_originalGLBilinear_annihilates_jointKernel
    (hFrozen : 0 < beta n) (k : Coeff) (hk : k ∈ JointKernel) (b : Coeff) :
    GLForm hFrozen k b = 0 ∧ GLForm hFrozen b k = 0 := by
  have hkB : k ∈ (B hFrozen).mulVecLin.ker := by
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen]
    exact hk
  have hz : (B hFrozen) *ᵥ k = 0 := (LinearMap.mem_ker).mp hkB
  have hPair := p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen b k
  rw [hz, dotProduct_zero] at hPair
  have hRight : GLForm hFrozen b k = 0 := hPair.symm
  exact ⟨(p4Q2HO_actualRightOriginalGLBilinear_symm
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen k b).trans hRight, hRight⟩

/-- There exists one finite genuine Wilson SU(2) context family on
which the true GL and sampled GI-SOS matrices have exactly the same
kernel, rank, and zero quadratic coefficients. -/
theorem p4Q2HP_actualRight_exists_finiteGL_SOS_common_certificate
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (B hFrozen).mulVecLin.ker = (R s).mulVecLin.ker ∧
      (B hFrozen).rank = (R s).rank ∧
      ∀ a : Coeff,
        (star a ⬝ᵥ ((B hFrozen) *ᵥ a) = 0 ↔
         star a ⬝ᵥ ((R s) *ᵥ a) = 0) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, ?_, ?_, ?_⟩
  · exact p4Q2HP_actualRight_originalGLGram_ker_eq_finiteSOSGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hs
  · exact p4Q2HP_actualRight_originalGLGram_rank_eq_finiteSOSGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hs
  · intro a
    exact p4Q2HP_actualRight_originalGLGram_quad_zero_iff_finiteSOSGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hs a

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_ker_eq_finiteSOSGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_rank_eq_finiteSOSGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_quad_zero_iff_finiteSOSGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_quad_pos_iff_finiteSOSGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLMass_pos_iff_not_mem_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_rank_le_physicalSourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_sourceSeparation_iff_originalGLGram_rank_eq_sourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLGram_rankLoss_iff_invisiblePhysicalSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_originalGLBilinear_annihilates_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HP_actualRight_exists_finiteGL_SOS_common_certificate
