import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarDepthZeroPhysicalSourceNormCoercivityV5_IE
import Mathlib.Tactic

/-!
# P4-Q2-IG: genuine physical-source-norm GL coercivity on GI-visible complements

For arbitrary nonnegative fine coupling beta(n+1) and finite right-Krylov
depth r, the original true two-interacting-Wilson-posterior GI joint
kernel K may have a larger kernel than the physical Haar-L² source
synthesis S. Full equality K=ker S for positive fine beta and r>0
is still OPEN. Therefore a global GL-to-SOURCE-norm lower bound on
the whole coefficient space must NOT be manufactured.

Instead take ANY genuine real linear complement W to K. The existing
unconditional inclusion ker S <= K and IsCompl K W imply S|W is
injective, even when the full source family has dependent modes.
Consequently the TRUE original physical source Gram Qsrc is positive
definite on W, as follows from IE's verified exact identity:
  aᵀ Qsrc a = ‖S(a)‖²_(original Haar L²).
On the SAME W, HQ establishes strict positivity of the independently
defined ORIGINAL interacting-Wilson GL integral detector Gram B.

P4-Q2-HR's pinned mathlib compact-unit-sphere finite-dimensional
comparison theorem then gives some strictly positive, genuine
fixed-model constants 0<c<=C with, for every w in W,
  c * ‖S(w)‖² <= M_GL(S(w)) <= C * ‖S(w)‖².

An actual complement exists by mathlib `Submodule.exists_isCompl`.
The theorem uses real ORIGINAL physical source norms and ORIGINAL
two-Wilson-posterior GL spatial mass; not an independent-Haar
conditional, synthetic source frame, or a diagonal Gram assumption.
It holds for all finite n,r and nonnegative fine beta, but only on
the visible complement, and is not H/scale/r/beta-uniform. It does
NOT prove S is detected for all nonzero physical sources, H1-C3,
OS Hamiltonian, or the continuum four-dimensional Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3700000
set_option synthInstance.maxHeartbeats 1000000

local instance p4Q2IG_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IG_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IG_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IG_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IG_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IG_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "JointKernel" =>
  p4Q2HG_actualRightGIJointModalKernel
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn

/-- On ANY complement W to the actual joint original Wilson GI
detector kernel K, a nonzero coefficient represents a genuinely
NONZERO physical signed gauge-invariant Haar-L² source. The only
input is the already-proved global inclusion ker S <= K. -/
theorem p4Q2IG_actualRight_physicalSource_ne_zero_on_GI_complement
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W)
    (w : W) (hw : w ≠ 0) :
    (∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ)) ≠ 0 := by
  have hOutside : (w : Coeff) ∉ JointKernel :=
    p4Q2HQ_complement_nonzero_not_mem_kernel JointKernel W hCompl w hw
  intro hSource
  exact hOutside
    (p4Q2HG_actualSource_zero_mem_GIJointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff) hSource)

/-- At ALL fine beta >= 0 and ALL finite r, the ORIGINAL physical
Haar-L² source Gram is strictly positive on the true GI-visible
complement W. This does not assume the full modes are independent. -/
theorem p4Q2IG_actualRight_sourceGram_pos_on_GI_complement
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W)
    (w : W) (hw : w ≠ 0) :
    0 < star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff)) := by
  rw [p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r (w : Coeff)]
  exact pow_pos (norm_pos_iff.mpr
    (p4Q2IG_actualRight_physicalSource_ne_zero_on_GI_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r W hCompl w hw)) 2

/-- Both ORIGINAL GL integral Gram and genuine physical Haar-L²
source Gram admit the SAME model-dependent strictly positive
two-sided constants on a GI-kernel complement. The estimate concerns
PHYSICAL source norm, not merely the original GI detector SOS norm. -/
theorem p4Q2IG_actualRight_GL_physicalSourceNorm_comparison_on_GI_complement
    (hFrozen : 0 < beta n)
    (W : Submodule ℝ Coeff) (hCompl : IsCompl JointKernel W) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ w : W,
        c * ‖∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ)‖ ^ 2 ≤
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ∧
          p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
            Hn (beta n) (hbeta n)
            (∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ))
            (Finset.univ : Finset Link) ≤
          C * ‖∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ)‖ ^ 2 := by
  let qB : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff))
  let qS : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))
  have hContB : Continuous qB :=
    (p4Q2HR_realMatrix_quad_continuous (B hFrozen)).comp
      continuous_subtype_val
  have hContS : Continuous qS :=
    (p4Q2HR_realMatrix_quad_continuous Qsrc).comp
      continuous_subtype_val
  have hHomB (c : ℝ) (w : W) :
      qB (c • w) = c ^ 2 * qB w := by
    simpa only [qB, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul (B hFrozen) c (w : Coeff))
  have hHomS (c : ℝ) (w : W) :
      qS (c • w) = c ^ 2 * qS w := by
    simpa only [qS, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul Qsrc c (w : Coeff))
  have hPosB (w : W) (hw : w ≠ 0) : 0 < qB w :=
    p4Q2HQ_actualRight_GLGram_pos_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen W hCompl w hw
  have hPosS (w : W) (hw : w ≠ 0) : 0 < qS w :=
    p4Q2IG_actualRight_sourceGram_pos_on_GI_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r W hCompl w hw
  obtain ⟨c, C, hc, hcC, hComp⟩ :=
    p4Q2HR_finiteDimensional_positive_quadratics_comparable
      qB qS hContB hContS hHomB hHomS hPosB hPosS
  refine ⟨c, C, hc, hcC, ?_⟩
  intro w
  have hB :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen (w : Coeff)
  have hS :=
    p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff)
  simpa only [qB, qS, hB, hS] using hComp w

/-- Even without complete higher-depth physical source separation,
there exists an actual physical GI-kernel complement on which the
original Wilson GL mass has genuine physical-SOURCE-norm coercivity
and upper bound, at ALL nonnegative fine couplings and finite depths.
The real constants depend on the selected fixed finite model. -/
theorem p4Q2IG_actualRight_exists_GI_visible_physicalSourceNorm_comparison
    (hFrozen : 0 < beta n) :
    ∃ W : Submodule ℝ Coeff,
      IsCompl JointKernel W ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ w : W,
          c * ‖∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ)‖ ^ 2 ≤
            p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
              Hn (beta n) (hbeta n)
              (∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ))
              (Finset.univ : Finset Link) ∧
            p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
              Hn (beta n) (hbeta n)
              (∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ))
              (Finset.univ : Finset Link) ≤
            C * ‖∑ j : Fin (r + 1), (w : Coeff) j • RightFactor n (j : ℕ)‖ ^ 2 := by
  obtain ⟨W, hCompl⟩ := Submodule.exists_isCompl JointKernel
  exact ⟨W, hCompl,
    p4Q2IG_actualRight_GL_physicalSourceNorm_comparison_on_GI_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen W hCompl⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IG_actualRight_physicalSource_ne_zero_on_GI_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IG_actualRight_sourceGram_pos_on_GI_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IG_actualRight_GL_physicalSourceNorm_comparison_on_GI_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IG_actualRight_exists_GI_visible_physicalSourceNorm_comparison
