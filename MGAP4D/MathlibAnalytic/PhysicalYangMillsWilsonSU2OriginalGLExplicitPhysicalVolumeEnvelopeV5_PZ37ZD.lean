import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullLinkGLPhysicalHilbertUpperV5_PZ37ZC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSharpPhysicalD3MassV5_PZ37Y
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZD — explicit original full-link GL / physical Gram upper envelope

The EXACT original two-interacting-Wilson-posterior, all-spatial-link,
all-boundary-context GL Haar mass was proved in PZ37ZC to satisfy

  M_GL(f) ≤ 2 |Links(H)| exp(16 b) ||f||²

for EVERY genuine Gauss-law physical Haar-L² source. This file transports
that inequality through HO's ORIGINAL GL INTEGRAL matrix and IE's
ORIGINAL physical source Gram at ALL finite right-Krylov depths. Its
explicit upper constant depends ONLY on the actual spatial-link
cardinality and frozen coupling b, NOT on fine t, depth or the choice
of physical boundary contexts.

We deliberately add a harmless 1 to get a manifestly positive
constant without any separate cardinality/nonempty API assumption:

  Cexp(H,b) := 1 + 2 |Links(H)| / exp(-16 b).

For the original finite-three Wilson Hankel Gram P and true original
integrated posterior GL Gram B the genuine all-coefficient quadratic
inequality gives B ≤ Cexp P and hence trace(B) ≤ Cexp trace(P).
The previously established positive LOWER comparison c_H P ≤ B
and sharp determinant lower c_H³ D3 > 0 are retained and NOT assumed
volume-uniform. This eliminates the unnamed upper comparison constant
from the finite-volume upper trace envelope, without inventing a
uniform positive lower bound.

Neither compactness of the original detector nor an all-physical-space
coercivity floor is claimed; no proxy posterior, Dobrushin, new axiom,
sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZD_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- An explicit positive original-Wilson upper comparison factor,
uniform in fine coupling and source depth at fixed original H,b.
The unscaled coefficient before adding 1 is precisely PZ37ZC's
full-link Hilbert-upper factor. -/
noncomputable def p4Q2PZ37ZD_originalGL_upperEnvelope
    (H : ℕ) (b : ℝ) : ℝ :=
  1 + ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
    2) / Real.exp (-16 * b)

theorem p4Q2PZ37ZD_originalGL_upperEnvelope_pos
    (H : ℕ) (b : ℝ) :
    0 < p4Q2PZ37ZD_originalGL_upperEnvelope H b := by
  unfold p4Q2PZ37ZD_originalGL_upperEnvelope
  have hCard : (0 : ℝ) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) :=
    Nat.cast_nonneg _
  have hExp : 0 < Real.exp (-16 * b) := Real.exp_pos _
  have hTerm : 0 ≤
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * 2) /
        Real.exp (-16 * b) :=
    div_nonneg (mul_nonneg hCard (by norm_num)) hExp.le
  linarith

section GenuineOriginalFullLinkGram

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Src" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Qsrc" =>
  p4Q2HM_actualRightPhysicalHaarL2SourceGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)
local notation "Cexp" =>
  p4Q2PZ37ZD_originalGL_upperEnvelope Hn (beta n)

/-- The ACTUAL all-link/all-context posterior GL integral matrix obeys
an EXPLICIT upper quadratic comparison against the ACTUAL Gauss-law
Haar-L² physical source Gram at ALL finite right-Krylov depths,
including dependent modes and fine=0. The original frozen b>0
and genuine two Wilson posterior laws are unchanged. -/
theorem p4Q2PZ37ZD_allFinite_allDepth_originalGL_explicitPhysicalGramUpper
    (hFrozen : 0 < beta n) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
      Cexp * (star a ⬝ᵥ (Qsrc *ᵥ a)) := by
  have hSourceGram :
      star a ⬝ᵥ (Qsrc *ᵥ a) = ‖Src a‖ ^ 2 := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2IE_actualRightPhysicalSourceGram_quad_eq_sourceNormSq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hGLExact :
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) =
        Mass (Src a) (Finset.univ : Finset Link) := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r hFrozen a)
  have hUniversal :=
    p4Q2PZ37ZC_originalGL_fullLink_le_explicit_physicalSourceNorm
      Hn (beta n) hFrozen (Src a)
  have hNormNonneg : 0 ≤ ‖Src a‖ ^ 2 := sq_nonneg _
  calc
    star a ⬝ᵥ ((B hFrozen) *ᵥ a) =
        Mass (Src a) (Finset.univ : Finset Link) := hGLExact
    _ ≤ ((Fintype.card Link : ℝ) * (2 * ‖Src a‖ ^ 2)) /
          Real.exp (-16 * beta n) := hUniversal
    _ = (((Fintype.card Link : ℝ) * 2) /
          Real.exp (-16 * beta n)) * ‖Src a‖ ^ 2 := by ring
    _ ≤ (1 + (((Fintype.card Link : ℝ) * 2) /
          Real.exp (-16 * beta n))) * ‖Src a‖ ^ 2 := by
            nlinarith
    _ = Cexp * (star a ⬝ᵥ (Qsrc *ᵥ a)) := by
          rw [hSourceGram]
          rfl

end GenuineOriginalFullLinkGram

section GenuineThreeModeVolumeTrace

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "P" =>
  p4Q2PD_originalWilsonThreeHankel
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Cexp" =>
  p4Q2PZ37ZD_originalGL_upperEnvelope Hn (beta n)

/-- In the actual three-mode physical Gauss-law/Hankel presentation,
the full-link integrated GL Gram is controlled ABOVE by the explicit
original Wilson link-count factor Cexp in ALL real coefficients.
This holds for every nonnegative fine coupling, even fine zero. -/
theorem p4Q2PZ37ZD_allFinite_allFine_originalThreeGL_explicitHankelUpper
    (hFrozen : 0 < beta n) (a : Fin 3 → ℝ) :
    star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
      Cexp * (star a ⬝ᵥ (P *ᵥ a)) := by
  have hGram :
      p4Q2HM_actualRightPhysicalHaarL2SourceGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 2 = P := by
    simpa only [p4Q2HM_actualRightPhysicalHaarL2SourceGram,
      p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  have hUpper :=
    p4Q2PZ37ZD_allFinite_allDepth_originalGL_explicitPhysicalGramUpper
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen a
  rwa [hGram] at hUpper

/-- The ORIGINAL integrated GL matrix trace admits a fully explicit
UPPER factor Cexp times the genuinely interacting finite-H physical
moment trace (m0+m2+m4). A positive lower factor c still exists
from PZ37U/W but may depend on volume, fine and the true context.
No additional lower estimate is silently assumed. -/
theorem p4Q2PZ37ZD_allFinite_allFine_originalGL_explicitTraceSandwich
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    ∃ c : ℝ, 0 < c ∧
      c * (P).trace ≤ (B hFrozen).trace ∧
      (B hFrozen).trace ≤ Cexp * (P).trace := by
  obtain ⟨c, _C, hc, _hcC, hCmp⟩ :=
    p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀
  have hUpper :=
    p4Q2PZ37ZD_allFinite_allFine_originalThreeGL_explicitHankelUpper
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen
  have hBoth : ∀ a : Fin 3 → ℝ,
      c * (star a ⬝ᵥ (P *ᵥ a)) ≤
        star a ⬝ᵥ ((B hFrozen) *ᵥ a) ∧
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
        Cexp * (star a ⬝ᵥ (P *ᵥ a)) := by
    intro a
    exact ⟨(hCmp a).1, hUpper a⟩
  obtain ⟨hLow, hHi⟩ :=
    p4Q2PZ37W_finThree_quadratic_compare_trace P (B hFrozen) c Cexp hBoth
  exact ⟨c, hc, hLow, hHi⟩

end GenuineThreeModeVolumeTrace
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZD_originalGL_upperEnvelope_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZD_allFinite_allDepth_originalGL_explicitPhysicalGramUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZD_allFinite_allFine_originalThreeGL_explicitHankelUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZD_allFinite_allFine_originalGL_explicitTraceSandwich
