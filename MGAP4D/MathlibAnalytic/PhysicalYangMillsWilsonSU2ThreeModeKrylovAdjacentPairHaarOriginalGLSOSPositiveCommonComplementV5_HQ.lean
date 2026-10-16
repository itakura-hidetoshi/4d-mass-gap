import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualGIFiniteSumSquaresDetectionGramV5_HN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralDetectorMatrixV5_HO
import Mathlib.Tactic

/-!
# P4-Q2-HQ: a common genuinely positive detector complement

The actual original Wilson GL integral Gram B and the finite genuine GI
sum-of-squares Gram R=MᵀM vanish on exactly the same all-context kernel K.
Choose any REAL algebraic complement W of K in the finite genuine
fine-right Krylov coefficient space.

B and R both have STRICTLY positive quadratic value on every nonzero
w in W, with neither a physical source-frame hypothesis nor a claim
that K=ker S. This is the mathematically correct finite-dimensional
quotient positivity starting point for future fixed-volume norm comparison.
Even W=0 is allowed; strict positivity then holds vacuously.

Frozen beta(n)>0 is independent of nonnegative fine beta(n+1).
Haar in the B integral is the outer reference measure, NOT a substituted
independent Wilson posterior. No numerical comparison constants, volume
uniformity, H1-C3, OS Hamiltonian or continuum mass gap are asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HQ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HQ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HQ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HQ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HQ_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A nonzero element of a complement to K cannot lie inside K.
This pure module lemma needs no coordinate independence. -/
theorem p4Q2HQ_complement_nonzero_not_mem_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K W : Submodule ℝ E) (hCompl : IsCompl K W)
    (w : W) (hw : w ≠ 0) : (w : E) ∉ K := by
  intro hk
  have hBot : (w : E) ∈ (⊥ : Submodule ℝ E) := by
    rw [← hCompl.inf_eq_bot]
    exact ⟨hk, w.property⟩
  have hZero : (w : E) = 0 := by simpa using hBot
  exact hw (Subtype.ext hZero)

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
local notation "FiniteDetector" =>
  p4Q2HK_actualRightFiniteGIContextDetector
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

/-- The true original GL integral detector quadratic form is strictly
positive on a common complement of the authentic all-context GI kernel.
No positivity of every nonzero physical source is inferred. -/
theorem p4Q2HQ_actualRight_GLGram_pos_on_complement
    (hFrozen : 0 < beta n)
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W)
    (w : W) (hw : w ≠ 0) :
    0 < star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) := by
  have hOutside : (w : Coeff) ∉ JointKernel :=
    p4Q2HQ_complement_nonzero_not_mem_kernel JointKernel W hCompl w hw
  have hNonneg : 0 ≤ star (w : Coeff) ⬝ᵥ
      ((B hFrozen) *ᵥ (w : Coeff)) :=
    (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).dotProduct_mulVec_nonneg (w : Coeff)
  have hZero :
      (star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) = 0) ↔
      (w : Coeff) ∈ JointKernel := by
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (w : Coeff)]
    exact p4Q2HI_actualRightGLMass_zero_iff_GI_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (w : Coeff)
  have hNotZero :
      star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) ≠ 0 :=
    fun hz => hOutside (hZero.mp hz)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNotZero)

/-- On the SAME complement and exact SU(2) detector finite context
family the original two-posterior squared Gram is strictly positive. -/
theorem p4Q2HQ_actualRight_SOSGram_pos_on_complement
    (s : Finset Context) (hExact : (FiniteDetector s).ker = JointKernel)
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W)
    (w : W) (hw : w ≠ 0) :
    0 < star (w : Coeff) ⬝ᵥ ((R s) *ᵥ (w : Coeff)) := by
  have hOutside : (w : Coeff) ∉ JointKernel :=
    p4Q2HQ_complement_nonzero_not_mem_kernel JointKernel W hCompl w hw
  exact p4Q2HN_actualRight_GIGram_quad_pos_of_not_mem_jointKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r s hExact (w : Coeff) hOutside

/-- The actual Wilson GL bilinear form is positive definite when
restricted to ANY chosen complement of the all-context GI kernel. -/
theorem p4Q2HQ_actualRight_GLBilinear_pos_on_complement
    (hFrozen : 0 < beta n)
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W)
    (w : W) (hw : w ≠ 0) :
    0 < GLForm hFrozen (w : Coeff) (w : Coeff) := by
  rw [← p4Q2HO_actualRightOriginalGLIntegralMatrix_pairing
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen (w : Coeff) (w : Coeff)]
  exact p4Q2HQ_actualRight_GLGram_pos_on_complement
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen W hCompl w hw

/-- The TRUE Wilson physical problem provides a common algebraic
complement on which both genuine detectors are strictly positive.
The subspace may be zero; hence this does not assert a nonzero GI anchor.
It is a finite-volume statement and yields no universal comparison yet. -/
theorem p4Q2HQ_actualRight_exists_common_positive_detector_complement
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context, ∃ W : Submodule ℝ Coeff,
      (FiniteDetector s).ker = JointKernel ∧
      IsCompl JointKernel W ∧
      ∀ w : W, w ≠ 0 →
        0 < star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) ∧
        0 < star (w : Coeff) ⬝ᵥ ((R s) *ᵥ (w : Coeff)) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  obtain ⟨W, hCompl⟩ := JointKernel.exists_isCompl
  refine ⟨s, W, hs, hCompl, ?_⟩
  intro w hw
  exact ⟨
    p4Q2HQ_actualRight_GLGram_pos_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen W hCompl w hw,
    p4Q2HQ_actualRight_SOSGram_pos_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r s hs W hCompl w hw⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HQ_complement_nonzero_not_mem_kernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HQ_actualRight_GLGram_pos_on_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HQ_actualRight_SOSGram_pos_on_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HQ_actualRight_GLBilinear_pos_on_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HQ_actualRight_exists_common_positive_detector_complement
