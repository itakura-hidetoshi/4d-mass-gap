import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLPhysicalSourceGlobalCoercivityCriterionV5_IJ
import Mathlib.Tactic

/-!
# P4-Q2-IK: unconditional fixed-volume ORIGINAL Wilson GL physical-source upper bound

IJ proved that a strictly positive physical-source-norm LOWER bound for
the ACTUAL original two-interacting-Wilson-posterior GL spatial mass
exists (with a finite upper bound) precisely when the true physical
Haar-L² source synthesis kernel equals the true original GI detector
common kernel, ker S=K. That equality remains open for positive fine
coupling beta(n+1)>0 and Krylov depth r>0.

The UPPER direction does NOT need source separation.

The original actual physical Haar-L² source Gram Qsrc and the original
interacting Wilson GL integral Gram B are separate Hermitian positive
semidefinite real finite matrices. On a complement to ker S the ACTUAL
source Gram Qsrc is strictly positive. Even if B has extra detector-null
directions, the SUM of the two quadratic forms (B+Qsrc) is strictly
positive on that complement. Pinned mathlib/HR finite-dimensional
compact-unit-sphere comparison therefore bounds B by C*Qsrc there.

Every signed coefficient splits into ker S plus that complement.
Both the original Wilson GL spatial mass and actual source norm depend
only on the physical source S(a), so the bound extends to ALL signed
coefficients without any hidden assumption K=ker S.

The result is:
  For every finite n,r, frozen beta(n)>0, fine beta(n+1)>=0,
  exists C>0 such that for EVERY actual signed fine-right coefficient a,
    0 <= OriginalGLMass(S(a)) <= C * ‖S(a)‖².
The constant C is fixed-model-only, not uniform in physical volume,
frozen beta, spacing, lattice scale or depth. No lower bound is claimed
unless the IJ source-separation criterion holds. Neither independent
Haar conditional, Dobrushin estimate, H1-C3, OS Hamiltonian, nor the
continuum Yang--Mills mass gap is supplied.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1100000

local instance p4Q2IK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2IK_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualRight

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Coeff" => Fin (r + 1) → ℝ
local notation "PhysicalSource" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "OriginalMass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- TRUE original Wilson spatial GL mass has a model-dependent UPPER
bound in the actual physical source Haar-L² norm on the ENTIRE
signed finite right-Krylov coefficient space, no matter whether the
physical source S is fully detected by the joint GI detector. -/
theorem p4Q2IK_originalWilsonGLMass_global_physicalSourceNorm_upper
    (hFrozen : 0 < beta n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : Coeff,
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
          C * ‖PhysicalSource a‖ ^ 2 := by
  obtain ⟨W, hCompl⟩ := Submodule.exists_isCompl (PhysicalSource).ker
  let qB : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff))
  let qS : W → ℝ :=
    fun w => star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))
  let qSum : W → ℝ := fun w => qB w + qS w
  have hContB : Continuous qB :=
    (p4Q2HR_realMatrix_quad_continuous (B hFrozen)).comp
      continuous_subtype_val
  have hContS : Continuous qS :=
    (p4Q2HR_realMatrix_quad_continuous Qsrc).comp
      continuous_subtype_val
  have hContSum : Continuous qSum := hContB.add hContS
  have hHomB (t : ℝ) (w : W) :
      qB (t • w) = t ^ 2 * qB w := by
    simpa only [qB, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul (B hFrozen) t (w : Coeff))
  have hHomS (t : ℝ) (w : W) :
      qS (t • w) = t ^ 2 * qS w := by
    simpa only [qS, Submodule.coe_smul] using
      (p4Q2HR_realMatrix_quad_smul Qsrc t (w : Coeff))
  have hHomSum (t : ℝ) (w : W) :
      qSum (t • w) = t ^ 2 * qSum w := by
    change qB (t • w) + qS (t • w) =
      t ^ 2 * (qB w + qS w)
    rw [hHomB, hHomS]
    ring
  have hBNonneg (w : W) : 0 ≤ qB w :=
    (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).dotProduct_mulVec_nonneg (w : Coeff)
  have hSNonneg (w : W) : 0 ≤ qS w := by
    change 0 ≤ star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))
    rw [p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff)]
    exact sq_nonneg _
  have hSPos (w : W) (hw : w ≠ 0) : 0 < qS w := by
    have hOutside : (w : Coeff) ∉ (PhysicalSource).ker :=
      p4Q2HQ_complement_nonzero_not_mem_kernel
        (PhysicalSource).ker W hCompl w hw
    have hActualSource : PhysicalSource (w : Coeff) ≠ 0 := by
      intro hZero
      exact hOutside ((LinearMap.mem_ker).mpr hZero)
    change 0 < star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))
    rw [p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (w : Coeff)]
    exact pow_pos (norm_pos_iff.mpr hActualSource) 2
  have hSumPos (w : W) (hw : w ≠ 0) : 0 < qSum w := by
    change 0 < qB w + qS w
    exact add_pos_of_nonneg_of_pos (hBNonneg w) (hSPos w hw)
  obtain ⟨c, C, hc, hcC, hComparison⟩ :=
    p4Q2HR_finiteDimensional_positive_quadratics_comparable
      qSum qS hContSum hContS hHomSum hHomS hSumPos hSPos
  have hUpper (w : W) : qB w ≤ C * qS w := by
    have h := (hComparison w).2
    change qB w + qS w ≤ C * qS w at h
    linarith [hSNonneg w]
  refine ⟨C, lt_of_lt_of_le hc hcC, ?_⟩
  intro a
  have haTop : a ∈ (PhysicalSource).ker ⊔ W := by
    rw [hCompl.codisjoint.eq_top]
    trivial
  obtain ⟨k, w, hkw⟩ := (Submodule.mem_sup').mp haTop
  have hkZero : PhysicalSource (k : Coeff) = 0 :=
    (LinearMap.mem_ker).mp k.property
  have hSourceEq : PhysicalSource a = PhysicalSource (w : Coeff) := by
    calc
      PhysicalSource a = PhysicalSource ((k : Coeff) + (w : Coeff)) := by
        rw [hkw]
      _ = PhysicalSource (k : Coeff) + PhysicalSource (w : Coeff) := by
        rw [map_add]
      _ = PhysicalSource (w : Coeff) := by
        rw [hkZero, zero_add]
  have hW :
      OriginalMass (PhysicalSource (w : Coeff))
          (Finset.univ : Finset Link) ≤
      C * ‖PhysicalSource (w : Coeff)‖ ^ 2 := by
    have h := hUpper w
    change star (w : Coeff) ⬝ᵥ ((B hFrozen) *ᵥ (w : Coeff)) ≤
      C * (star (w : Coeff) ⬝ᵥ ((Qsrc) *ᵥ (w : Coeff))) at h
    rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen (w : Coeff),
      p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (w : Coeff)] at h
    exact h
  rw [hSourceEq]
  exact hW

/-- No positivity of the physical source in EVERY GI direction is
assumed: the ORIGINAL Wilson mass is simply nonnegative and bounded
above by a positive fixed-finite-model multiple of the actual
physical Haar-L² signed-source squared norm for ALL coefficients. -/
theorem p4Q2IK_originalWilsonGLMass_global_nonneg_and_physicalSourceNorm_upper
    (hFrozen : 0 < beta n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : Coeff,
        0 ≤ OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ∧
        OriginalMass (PhysicalSource a) (Finset.univ : Finset Link) ≤
          C * ‖PhysicalSource a‖ ^ 2 := by
  obtain ⟨C, hC, hUpper⟩ :=
    p4Q2IK_originalWilsonGLMass_global_physicalSourceNorm_upper
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen
  refine ⟨C, hC, ?_⟩
  intro a
  have hNonneg : 0 ≤ star a ⬝ᵥ ((B hFrozen) *ᵥ a) :=
    (p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFrozen).dotProduct_mulVec_nonneg a
  rw [p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r hFrozen a] at hNonneg
  exact ⟨hNonneg, hUpper a⟩

end ActualRight
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IK_originalWilsonGLMass_global_physicalSourceNorm_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IK_originalWilsonGLMass_global_nonneg_and_physicalSourceNorm_upper
