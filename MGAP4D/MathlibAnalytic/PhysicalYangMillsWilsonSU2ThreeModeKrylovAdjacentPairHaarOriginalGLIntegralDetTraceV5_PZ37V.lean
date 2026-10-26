import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPosteriorPhysicalCoercivityV5_PZ37U
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# P4-Q2-PZ37V — genuine Wilson GL integral determinant/trace coercivity

PZ37U proves, without a new axiom, that the original interacting
two-posterior Haar gap-square mass is uniformly coercive in ALL three
real Krylov coefficients at every fixed finite volume and sufficiently
small positive fine coupling. Its positive comparison coefficient is
not explicit.

The genuine GL integral detector matrix constructed in HO has entries
  G^GL_ij = sum_e integral Delta_i(e,z)*Delta_j(e,z)/Q_e(z) d Haar_pair(z).
HO proves that its exact quadratic form is the UNMODIFIED original
posterior mass. From PZ37U's existing positive coefficient floor,
this module first proves that the ACTUAL 3x3 GL integral Gram is positive
definite (hence its actual determinant is positive). The existing
PZ37R/PZ37T spectral lemmas then eliminate the unknown comparison
constant from the final coefficient floor:

   (4 det G^GL / (trace G^GL)^2) * sum_(j=0..2) a_j^2
       <= original_GL_mass(S_2 a).

This is the authentic original SU(2) Wilson/Haar posterior detector
rather than a surrogate Gaussian statistic, a finite sampled GI SOS
matrix, or the distinct physical source Gram.

The determinant, trace, positive small-fine radius and resulting bound
are volume/coupling dependent. No positive inf_H lower bound for
the volume-normalized posterior mass Q_GI/N_H (U0), no common positive
fine-radius for arbitrary depth, endpoint, strong limit, Hamiltonian
or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37V_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37V_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37V_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37V_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37V_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37V_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalPosteriorThreeGram
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
local notation "GL" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- The genuine original Wilson GL INTEGRAL detector matrix is
strictly positive definite for the actual three fine-right modes.
This follows from PZ37U's true mass floor for all coefficients, rather
than a positive determinant assumption or substituted posterior. -/
theorem p4Q2PZ37V_allFiniteSmallFine_originalGLIntegralGram_posDef
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (GL hFrozen).PosDef) := by
  obtain ⟨delta, hdelta, hFloor⟩ :=
    p4Q2PZ37U_allFiniteSmallFine_originalPosteriorMass_explicitGramFloor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨hB, c, C, hc, hcC, hBound⟩ := hFloor hFine hSmall
  let G : Matrix (Fin 3) (Fin 3) ℝ := GL hFrozen
  have hPSD : G.PosSemidef :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen
  have hPos : G.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hPSD.isHermitian
    intro a ha
    have hCoeff : 0 < ∑ j : Fin 3, (a j) ^ 2 := by
      simpa [dotProduct, pow_two] using
        (dotProduct_star_self_pos_iff.mpr ha)
    have hMassPos :
        0 < Mass (Src a) (Finset.univ : Finset Link) := by
      have hCoeffFloor := (hBound a).1
      exact lt_of_lt_of_le (mul_pos (mul_pos hc hB) hCoeff) hCoeffFloor
    have hExact :
        star a ⬝ᵥ (G *ᵥ a) =
          Mass (Src a) (Finset.univ : Finset Link) := by
      simpa only [G, p4Q2HJ_actualRightPhysicalSourceSynthesis] using
        (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n 2 hFrozen a)
    rw [hExact]
    exact hMassPos
  exact hPos

/-- Eliminate the unnamed posterior/source comparison coefficient:
the strictly positive coefficient floor is directly the determinant
and trace of HO's genuinely interacting two-Wilson-posterior Haar
integral 3x3 matrix, not the independent physical Hankel Gram.
All three components of the new certificate are simultaneously valid
on the same finite-volume small-positive-fine interval. -/
theorem p4Q2PZ37V_allFiniteSmallFine_originalGLIntegral_detTrace_coercivity
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < (GL hFrozen).det ∧
        0 < 4 * (GL hFrozen).det / ((GL hFrozen).trace ^ 2) ∧
        ∀ a : Fin (2 + 1) → ℝ,
          (4 * (GL hFrozen).det / ((GL hFrozen).trace ^ 2)) *
              (∑ j : Fin (2 + 1), (a j) ^ 2) ≤
            Mass (Src a) (Finset.univ : Finset Link)) := by
  obtain ⟨delta, hdelta, hDef⟩ :=
    p4Q2PZ37V_allFiniteSmallFine_originalGLIntegralGram_posDef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  let G : Matrix (Fin 3) (Fin 3) ℝ := GL hFrozen
  have hPosDef : G.PosDef := hDef hFine hSmall
  have hPSD : G.PosSemidef :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen
  have hDet : 0 < G.det := hPosDef.det_pos
  obtain ⟨hLowerPos, hEig⟩ :=
    p4Q2PZ37R_finThree_posSemidef_eigenvalue_explicit_lower
      G hPSD hDet
  refine ⟨hDet, hLowerPos, ?_⟩
  intro a
  have hSpectral :=
    p4Q2PZ37T_finThree_posSemidef_spectral_quadratic_lower
      G hPSD (4 * G.det / (G.trace ^ 2)) hEig a
  have hExact :
      star a ⬝ᵥ (G *ᵥ a) =
        Mass (Src a) (Finset.univ : Finset Link) := by
    simpa only [G, p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 hFrozen a)
  rw [hExact] at hSpectral
  exact hSpectral

end OriginalPosteriorThreeGram
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37V_allFiniteSmallFine_originalGLIntegralGram_posDef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37V_allFiniteSmallFine_originalGLIntegral_detTrace_coercivity
