import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualSourceGramAndGIContextMatrixV5_HM
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P4-Q2-HN: true finite Wilson GI sum-of-squares detector Gram certificate

HM defined TWO actual finite matrices on the genuine signed fine-right physical
Krylov coefficient domain: the Haar-L² SOURCE Gram Qsrc of the physical modes,
and the rectangular two-interacting-Wilson-posterior GI expectation gap M,
whose rows are actual SU(2) physical link and pair-boundary contexts.

For any such M, define the symmetric FINITE DETECTOR Gram R = Mᵀ M, distinct
from Qsrc, from the pair-Haar residual Gram, and from GL's density contrast Q.
Pinned mathlib's real transpose-Gram theorems establish:
  R >= 0; ker R = ker M; rank R = rank M;
  aᵀ R a = sum_(true contexts x) (M a)_x².
Therefore the finite squared detection energy is zero exactly when every
selected original Wilson GI expectation-gap observation is zero, without
needing a singleton Haar atom or independence of physical Krylov modes.

For any HK exact finite-context certificate, this kernel equals the genuine
all-link/all-boundary GI common kernel K. At positive FROZEN beta, vanishing of
the original Wilson GL gap-square outer pair-Haar mass is equivalent to
vanishing of this finite sum of squares. A positive finite detector quadratic
value means the genuine GI response is nonzero, but DOES NOT provide a
numerical lower bound for the actual GL integral mass from finite samples.

The only outstanding physical source separation condition is STILL the
unproved equality rank R = rank Qsrc, equivalently ker S = K; if the ranks
differ, an actual nonzero physical source is invisible to all GI contexts.
No synthetic posterior, explicit point choice, volume-uniform physical frame,
H1-C3, OS Hamiltonian, or continuum four-dimensional mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HN_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Generic finite real detector row Gram is positive semidefinite. -/
theorem p4Q2HN_realDetectorGram_posSemidef
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) : (Mᵀ * M).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self M)

/-- Finite detector Gram and the original linear detector have EXACTLY the
same kernel even when the rectangular detector has dependent rows. -/
theorem p4Q2HN_realDetectorGram_ker_eq_detector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) :
    (Mᵀ * M).mulVecLin.ker = M.mulVecLin.ker := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.ker_mulVecLin_conjTranspose_mul_self M)

/-- Taking the finite real Gram of the actual detector cannot create or
erase any detected image directions. -/
theorem p4Q2HN_realDetectorGram_rank_eq_detector
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) : (Mᵀ * M).rank = M.rank := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.rank_conjTranspose_mul_self M)

/-- An exact finite real sum-of-squares representation, without passing
through a hypothetical conditional probability or a lattice limit. -/
theorem p4Q2HN_realDetectorGram_quad_eq_sumSquares
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) (a : ι → ℝ) :
    star a ⬝ᵥ ((Mᵀ * M) *ᵥ a) =
      ∑ x : κ, ((M *ᵥ a) x)^2 := by
  calc
    star a ⬝ᵥ ((Mᵀ * M) *ᵥ a) =
        (star a ᵥ* Mᵀ) ⬝ᵥ (M *ᵥ a) := by
          rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    _ = (M *ᵥ a) ⬝ᵥ (M *ᵥ a) := by
          simp only [Matrix.vecMul_transpose, Pi.star_apply, star_trivial]
    _ = ∑ x : κ, ((M *ᵥ a) x)^2 := by
          simp only [Matrix.dotProduct, pow_two]

/-- The zero locus of the real finite detector sum-of-squares is EXACTLY
the zero locus of the full rectangular detector, not merely a.e. nullity. -/
theorem p4Q2HN_realDetectorGram_quad_zero_iff_detector_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) (a : ι → ℝ) :
    star a ⬝ᵥ ((Mᵀ * M) *ᵥ a) = 0 ↔ M *ᵥ a = 0 := by
  rw [p4Q2HN_realDetectorGram_quad_eq_sumSquares]
  simpa only [Matrix.dotProduct, pow_two] using
    (Matrix.dotProduct_self_eq_zero (v := M *ᵥ a))

/-- The finite detector SOS is STRICTLY positive iff at least one genuine
detector coordinate is nonzero. No physical-source separation is inferred. -/
theorem p4Q2HN_realDetectorGram_quad_pos_iff_detector_ne_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix κ ι ℝ) (a : ι → ℝ) :
    0 < star a ⬝ᵥ ((Mᵀ * M) *ᵥ a) ↔ M *ᵥ a ≠ 0 := by
  rw [p4Q2HN_realDetectorGram_quad_eq_sumSquares]
  have hNonneg : 0 ≤ ∑ x : κ, ((M *ᵥ a) x)^2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  constructor
  · intro hPos hZero
    simp [hZero] at hPos
  · intro hNe
    have hDotNe : ∑ x : κ, ((M *ᵥ a) x)^2 ≠ 0 := by
      intro hZero
      apply hNe
      exact (p4Q2HN_realDetectorGram_quad_zero_iff_detector_zero M a).mp
        ((p4Q2HN_realDetectorGram_quad_eq_sumSquares M a).trans hZero)
    exact lt_of_le_of_ne hNonneg (Ne.symm hDotNe)

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

/-- ACTUAL finite GI source detector Gram of the original two INTERACTING
Wilson posterior expectation gaps, on the real fine-right Krylov
coefficient space. It is NOT the physical Haar-L² Gram Qsrc. -/
noncomputable def p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
    (s : Finset Context) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  (GI s)ᵀ * GI s

theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_posSemidef
    (s : Finset Context) :
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).PosSemidef :=
  p4Q2HN_realDetectorGram_posSemidef (GI s)

/-- Genuine original two-posterior GI detector Gram rank equals
the rank of the actual SU(2) context matrix from HM. -/
theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
    (s : Finset Context) :
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).rank = (GI s).rank :=
  p4Q2HN_realDetectorGram_rank_eq_detector (GI s)

/-- Every coefficient has a genuine finite squared-GI detection energy:
the EXACT sum of its original Wilson two-posterior gap squares at the
selected physical SU(2) link / boundary contexts. -/
theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_GISum
    (s : Finset Context) (a : Coeff) :
    star a ⬝ᵥ
      ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s) *ᵥ a) =
      ∑ x : s, ((GI s *ᵥ a) x)^2 :=
  p4Q2HN_realDetectorGram_quad_eq_sumSquares (GI s) a

/-- Each summand of the finite detector SOS is a SQUARED original
physical two-interacting-Wilson-posterior expectation difference
of the ACTUAL signed fine-right source, with no assumed source frame. -/
theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_actualSourceGI
    (s : Finset Context) (a : Coeff) :
    star a ⬝ᵥ
      ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s) *ᵥ a) =
      ∑ x : s,
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          Hn (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
          x.1.1 x.1.2)^2 := by
  rw [p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_GISum]
  apply Finset.sum_congr rfl
  intro x _hx
  have hMatrix :=
    p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s a
  have hMode :=
    p4Q2HF_actualRightGIExpectationGap_eq_modalLinear
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a x.1.1 x.1.2
  have hPoint := congrFun hMatrix x
  change ((GI s *ᵥ a) x)^2 =
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
      x.1.1 x.1.2)^2
  rw [hPoint]
  exact congrArg (fun t : ℝ => t ^ 2) hMode.symm

/-- At an HK EXACT finite-context certificate the positive-semidefinite
GI detection Gram has precisely the original ALL-CONTEXT physical GI kernel. -/
theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_ker_eq_jointKernel
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).mulVecLin.ker = JointKernel := by
  rw [p4Q2HN_realDetectorGram_ker_eq_detector]
  rw [p4Q2HM_actualRightOriginalGIContextMatrix_mulVecLin_eq_detector]
  exact hExact

/-- The authentic finite detector Gram rank never exceeds the rank
of the distinct ORIGINAL physical Haar-L² SOURCE Gram. -/
theorem p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_le_physicalGram
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s).rank ≤ Qsrc.rank := by
  rw [p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI]
  exact p4Q2HM_actualRight_originalGIMatrix_rank_le_physicalSourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact

/-- Quantitative physical-SOURCE separation condition, still OPEN:
equality of positive Gram ranks is EXACTLY the equality of physical
synthesis and original all-context GI detection kernels. -/
theorem p4Q2HN_actualRight_sourceSeparation_iff_GIGram_rank_eq_sourceGram
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    (PhysicalSource).ker = JointKernel ↔
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).rank = Qsrc.rank := by
  rw [p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI]
  exact (p4Q2HM_actualRight_sourceSeparation_iff_originalGI_matrixRanksEq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact).trans (eq_comm : Qsrc.rank = (GI s).rank ↔ _)

/-- A source is invisible to the actual finite GI detector exactly
when its genuine finite squared original Wilson GI energy vanishes. -/
theorem p4Q2HN_actualRight_GIGram_quad_zero_iff_finiteDetector_zero
    (s : Finset Context) (a : Coeff) :
    star a ⬝ᵥ
      ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s) *ᵥ a) = 0 ↔
      FiniteDetector s a = 0 := by
  rw [p4Q2HN_realDetectorGram_quad_zero_iff_detector_zero]
  exact (p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s a).congr_left

/-- For positive frozen beta, zero ORIGINAL spatial Wilson GL gap-square
mass is equivalent to zero finite physical GI sum of squares
at the finitely many ACTUAL contexts selected by HK. -/
theorem p4Q2HN_actualRight_GIGram_quad_zero_iff_originalGLMass_zero
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel)
    (hFrozen : 0 < beta n) (a : Coeff) :
    star a ⬝ᵥ
      ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s) *ᵥ a) = 0 ↔
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        Hn (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
        (Finset.univ : Finset Link) = 0 := by
  rw [p4Q2HN_actualRight_GIGram_quad_zero_iff_finiteDetector_zero]
  have hDetected : FiniteDetector s a = 0 ↔ a ∈ JointKernel := by
    rw [← LinearMap.mem_ker, hExact]
  exact hDetected.trans
    (p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen a).symm

/-- A strictly positive TRUE finite GI squared detector energy certifies
that the original GL gap-square mass is not zero, without claiming
any volume/spacing uniform lower bound. -/
theorem p4Q2HN_actualRight_GIGram_quad_pos_of_not_mem_jointKernel
    (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel)
    (a : Coeff) (hNot : a ∉ JointKernel) :
    0 < star a ⬝ᵥ
      ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s) *ᵥ a) := by
  rw [p4Q2HN_realDetectorGram_quad_pos_iff_detector_ne_zero]
  intro hZero
  have hKer : a ∈ (FiniteDetector s).ker := by
    apply (LinearMap.mem_ker).mpr
    rwa [← p4Q2HM_actualRightOriginalGIContextMatrix_mulVec_eq_detector]
  exact hNot (hExact ▸ hKer)

/-- HN gives an ACTUAL finite-original-Wilson-posterior SOS certificate
of the full GI kernel, finite rank bound and measured null locus, for
every signed fine-right physical Krylov family at frozen beta>0. -/
theorem p4Q2HN_actualRight_exists_finiteOriginalGI_SOS_certificate
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).mulVecLin.ker = JointKernel ∧
      (p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s).rank ≤ Qsrc.rank ∧
      ∀ a : Coeff,
        (star a ⬝ᵥ
          ((p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r s) *ᵥ a) = 0 ↔
         p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
           Hn (beta n) (hbeta n)
           (∑ j : Fin (r + 1), a j • RightFactor n (j : ℕ))
           (Finset.univ : Finset Link) = 0) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, ?_, ?_, ?_⟩
  · exact p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs
  · exact p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_le_physicalGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs
  · intro a
    exact p4Q2HN_actualRight_GIGram_quad_zero_iff_originalGLMass_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs hFrozen a

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_ker_eq_detector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_rank_eq_detector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_quad_eq_sumSquares
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_quad_zero_iff_detector_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_realDetectorGram_quad_pos_iff_detector_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_eq_GI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_GISum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_quad_eq_actualSourceGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_ker_eq_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRightOriginalGIFiniteSumSquaresGram_rank_le_physicalGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRight_sourceSeparation_iff_GIGram_rank_eq_sourceGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRight_GIGram_quad_zero_iff_finiteDetector_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRight_GIGram_quad_zero_iff_originalGLMass_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRight_GIGram_quad_pos_of_not_mem_jointKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HN_actualRight_exists_finiteOriginalGI_SOS_certificate
