import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFiniteGLSOSComplementComparisonV5_HR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSOSKernelQuadraticDescentV5_HS
import Mathlib.Tactic

/-!
# P4-Q2-HT: original Wilson fixed-volume whole-coefficient comparison

HR establishes genuine positive real finite comparison constants on ANY
complement W of the all-context GI kernel K for the two independent
physical detector Gram matrices:
 B = ORIGINAL two-interacting-Wilson-posterior GL pair-Haar integral Gram;
 R = the true finite two-Wilson-posterior GI sum-of-squares Gram MᵀM.

HS establishes exact invariance of BOTH quadratic forms under adding any
element of K. Every signed fine-right coefficient can be written
a = k + w with k in K and w in W. Therefore the SAME finite positive
constants compare the two original detector energies for EVERY a,
without needing physical source separation or fine-Krylov independence.

This is an exact theorem on a FIXED finite original Wilson model:
c and C can depend on volume H, n, r, frozen beta(n), fine beta(n+1),
and actual HK finite physical SU(2) contexts. It does not establish
the still-open equality K=ker(S), a uniform-in-volume/spacing/depth
frame, Dobrushin, H1-C3 reconstruction, OS Hamiltonian or any
continuum four-dimensional Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace ENNReal BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2HT_linksFintype (H : ℕ) :
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

/-- The genuine original pair-Haar GL detector quadratic form and the
exact finite genuine SU(2) Wilson-posterior GI SOS form are globally
comparable with strictly positive constants at each fixed finite model.
The comparison holds for ALL signed fine-right coefficient vectors,
even when the true physical source synthesis has dependent modes or
nontrivial GI-undetectable directions. -/
theorem p4Q2HT_actualRight_originalWilson_GL_SOS_global_fixed_comparison
    (hFrozen : 0 < beta n) (s : Finset Context)
    (hExact : (FiniteDetector s).ker = JointKernel) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Coeff,
        c * (star a ⬝ᵥ ((R s) *ᵥ a)) ≤
          star a ⬝ᵥ ((B hFrozen) *ᵥ a) ∧
        star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
          C * (star a ⬝ᵥ ((R s) *ᵥ a)) := by
  obtain ⟨W, hCompl⟩ :=
    Submodule.exists_isCompl
      (p4Q2HG_actualRightGIJointModalKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r)
  obtain ⟨c, C, hc, hcC, hW⟩ :=
    p4Q2HR_actualRight_Wilson_GL_SOS_comparison_on_complement
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen s hExact W hCompl
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  have ha : a ∈ JointKernel ⊔ W := by
    rw [hCompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, hk, w, hw, hsum⟩ := (Submodule.mem_sup).mp ha
  have hB :
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) =
        star w ⬝ᵥ ((B hFrozen) *ᵥ w) := by
    simpa only [hsum] using
      (p4Q2HS_actualRight_GL_quad_add_jointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen k hk w)
  have hR :
      star a ⬝ᵥ ((R s) *ᵥ a) =
        star w ⬝ᵥ ((R s) *ᵥ w) := by
    simpa only [hsum] using
      (p4Q2HS_actualRight_SOS_quad_add_jointKernel
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r s hExact k hk w)
  have hwBound := hW (⟨w, hw⟩ : W)
  simpa only [hB, hR] using hwBound

/-- Choose one exact finite original Wilson physical SU(2) context
certificate and positive finite constants. This statement contains
NO numerical value of these constants and NO uniformity in H,n,r. -/
theorem p4Q2HT_actualRight_exists_originalWilson_global_fixed_comparison
    (hFrozen : 0 < beta n) :
    ∃ s : Finset Context,
      (FiniteDetector s).ker = JointKernel ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ a : Coeff,
          c * (star a ⬝ᵥ ((R s) *ᵥ a)) ≤
            star a ⬝ᵥ ((B hFrozen) *ᵥ a) ∧
          star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
            C * (star a ⬝ᵥ ((R s) *ᵥ a)) := by
  obtain ⟨s, hs⟩ :=
    p4Q2HK_actualRightFiniteGIContextDetector_ker_eq_jointKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  refine ⟨s, hs, ?_⟩
  exact p4Q2HT_actualRight_originalWilson_GL_SOS_global_fixed_comparison
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen s hs

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HT_actualRight_originalWilson_GL_SOS_global_fixed_comparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HT_actualRight_exists_originalWilson_global_fixed_comparison
