import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSharpPhysicalD3MassV5_PZ37Y
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualRightTransferSourceKernelV5_HA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZB — exact fine-zero rank obstruction of the genuine full-link GL Gram

This is the ORIGINAL SU(2) Wilson two-INTERACTING-posterior GL Haar integral
over ALL physical spatial links and ALL pair-Haar boundary contexts (HO).
It is NOT the two-context, transfer-compensated local GI density ruled out
by PZ37ZA.

At the actual fine endpoint beta(n+1)=0, HA proves that the physical
three-mode source S_2(a) is the real coefficient sum times the genuine
Gauss-law constant unit. Thus a=(1,-1,0) is a NONZERO coefficient vector
whose genuine physical source vanishes. OX gives that the original full-link
posterior GL mass of precisely this source is ZERO, and HO identifies the
quadratic form of the actual GL integral matrix with this exact mass.

Consequences: the genuine 3x3 all-link GL Gram is positive semidefinite but
SINGULAR at fine zero; its determinant is exactly zero; no positive
coefficient-l2 Gram lower bound can hold when this endpoint is included.
This obstruction concerns the COEFFICIENT frame, not the still-valid
physical-source-norm comparison for the original full-link posterior mass.
In particular it does not rule out a volume-uniform physical-source GL
coercivity estimate or any fine-positive-only estimate.

The frozen Wilson beta(n)>0 remains distinct from the fine beta(n+1)=0.
No model replacement, Dobrushin, new axioms, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZB_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

private def p4Q2PZ37ZB_cancel : Fin 3 → ℝ :=
  fun j => if j = 0 then 1 else if j = 1 then -1 else 0

private theorem p4Q2PZ37ZB_cancel_sum_zero :
    (∑ j : Fin 3, p4Q2PZ37ZB_cancel j) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [p4Q2PZ37ZB_cancel, Fin.sum_univ_three, h20, h21]

private theorem p4Q2PZ37ZB_cancel_norm_sq :
    (∑ j : Fin 3, (p4Q2PZ37ZB_cancel j) ^ 2) = 2 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [p4Q2PZ37ZB_cancel, Fin.sum_univ_three, h20, h21]

private theorem p4Q2PZ37ZB_cancel_ne_zero :
    p4Q2PZ37ZB_cancel ≠ (0 : Fin 3 → ℝ) := by
  intro h
  have h0 := congrArg (fun a : Fin 3 → ℝ => a 0) h
  norm_num [p4Q2PZ37ZB_cancel] at h0

section OriginalFullLinkGLFineZero

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Src" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The exact original full-link, all-context posterior GL Gram has a
nonzero coefficient cancellation at the physical fine-zero endpoint.
The mass of the corresponding REAL physical source is exactly zero. -/
theorem p4Q2PZ37ZB_fineZero_originalFullLinkGL_cancel_quadratic_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (e : Link) (left₀ : Cfg) :
    star p4Q2PZ37ZB_cancel ⬝ᵥ
        ((B hFrozen) *ᵥ p4Q2PZ37ZB_cancel) = 0 := by
  have hSrc : Src p4Q2PZ37ZB_cancel = 0 := by
    change
      (∑ j : Fin 3, p4Q2PZ37ZB_cancel j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) = 0
    exact (p4Q2HA_fineZero_actualSource_zero_iff_sum_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFineZero p4Q2PZ37ZB_cancel).mpr
        p4Q2PZ37ZB_cancel_sum_zero
  have hMassZero :
      Mass (Src p4Q2PZ37ZB_cancel) (Finset.univ : Finset Link) = 0 :=
    (p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ 2 p4Q2PZ37ZB_cancel).mpr hSrc
  have hExact :
      star p4Q2PZ37ZB_cancel ⬝ᵥ
          ((B hFrozen) *ᵥ p4Q2PZ37ZB_cancel) =
        Mass (Src p4Q2PZ37ZB_cancel)
          (Finset.univ : Finset Link) := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 hFrozen p4Q2PZ37ZB_cancel)
  exact hExact.trans hMassZero

/-- No coefficient-l2 coercivity can include the true fine-zero
endpoint, even after integrating the original detector over ALL
Wilson links and ALL actual pair-Haar contexts. -/
theorem p4Q2PZ37ZB_fineZero_no_positive_fullLinkGL_coefficient_frame
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (e : Link) (left₀ : Cfg) :
    ¬ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ a : Fin 3 → ℝ,
        gamma * (∑ j : Fin 3, (a j) ^ 2) ≤
          Mass (Src a) (Finset.univ : Finset Link) := by
  rintro ⟨gamma, hGamma, hLower⟩
  have hQZero :=
    p4Q2PZ37ZB_fineZero_originalFullLinkGL_cancel_quadratic_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen hFineZero e left₀
  have hExact :
      star p4Q2PZ37ZB_cancel ⬝ᵥ
          ((B hFrozen) *ᵥ p4Q2PZ37ZB_cancel) =
        Mass (Src p4Q2PZ37ZB_cancel)
          (Finset.univ : Finset Link) := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 hFrozen p4Q2PZ37ZB_cancel)
  have hMassZero :
      Mass (Src p4Q2PZ37ZB_cancel) (Finset.univ : Finset Link) = 0 :=
    hExact.symm.trans hQZero
  have hLowerCancel := hLower p4Q2PZ37ZB_cancel
  rw [p4Q2PZ37ZB_cancel_norm_sq, hMassZero] at hLowerCancel
  linarith

/-- This is a SINGULARITY theorem about the GENUINE full-link original
GL integral matrix itself: finite-H positive-frozen/fine-zero B is PSD
but cannot be positive definite, so its actual determinant vanishes. -/
theorem p4Q2PZ37ZB_fineZero_originalFullLinkGL_det_zero
    (hFrozen : 0 < beta n) (hFineZero : beta (n + 1) = 0)
    (e : Link) (left₀ : Cfg) :
    (B hFrozen).det = 0 := by
  have hPSD : (B hFrozen).PosSemidef :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen
  have hQZero :=
    p4Q2PZ37ZB_fineZero_originalFullLinkGL_cancel_quadratic_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen hFineZero e left₀
  have hNotDef : ¬ (B hFrozen).PosDef := by
    intro hDef
    have hStrict :
        0 < star p4Q2PZ37ZB_cancel ⬝ᵥ
          ((B hFrozen) *ᵥ p4Q2PZ37ZB_cancel) :=
      hDef.dotProduct_mulVec_pos p4Q2PZ37ZB_cancel_ne_zero
    rw [hQZero] at hStrict
    exact (lt_irrefl (0 : ℝ)) hStrict
  by_contra hDet
  exact hNotDef ((hPSD.posDef_iff_det_ne_zero).mpr hDet)

end OriginalFullLinkGLFineZero
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZB_fineZero_originalFullLinkGL_cancel_quadratic_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZB_fineZero_no_positive_fullLinkGL_coefficient_frame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZB_fineZero_originalFullLinkGL_det_zero
