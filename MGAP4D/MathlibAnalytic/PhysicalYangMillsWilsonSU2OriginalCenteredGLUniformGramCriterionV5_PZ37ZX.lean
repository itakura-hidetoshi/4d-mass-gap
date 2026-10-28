import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalFineRayleighLimitV5_PZ37ZW3
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZX — genuine centered Wilson GL Gram / volume-uniformity criterion

The genuine fixed-volume strict fine-zero Rayleigh limit (ZW3) is
expressed EXACTLY using the two-mode matrix constructed in ZP from the
original TWO interacting Wilson posteriors, ALL actual spatial links,
the ACTUAL full pair-Haar integral and variance denominators.

The centered spatial Wilson source V_H has coefficient vector
a_H = (-⟪W_H,U_H⟫/2, 1/2), with the second coordinate fixed at 1/2.
Hence every genuine ZP coefficient Gram floor m_(H,b)>0 gives

    M_GL(H,b;V_H) >= m_(H,b)/4
    Rayleigh(H,b;V_H) >= m_(H,b)/(4 ||V_H||^2).

We then give an EXACT equivalence, for arbitrary volume-indexed
positive frozen couplings b_H, between a shared lower bound c on
the true centered-Wilson physical Rayleigh limits and the whole-family
finite-original-Gram inequality

    c ||V_H||^2 <= a_H^T G_(H,b_H) a_H    for every H.

This states an authority boundary, not an unconditional volume-uniform
coercivity claim. ZP only proves separate m_(H,b)>0. Its dependence on
volume, beta and the physical Wilson source norm remains uncontrolled.

No new axioms, sorry/admit/native_decide, surrogate posterior,
compensated two-context no-go reversal, endpoint E/F, H1-H4 or
continuum 4D Yang–Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Matrix Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZX_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Literal original full-link and pair-Haar finite 2x2 Gram
evaluation in the actual ZW normalized centered Wilson direction. -/
noncomputable def p4Q2PZ37ZX_originalCenteredGLGramValue
    (H : ℕ) (b : ℝ) (hb : 0 < b) : ℝ :=
  let a := p4Q2PZ37ZW_originalCenteredCoefficients H
  star a ⬝ᵥ ((p4Q2PZ37ZP_originalStaticPhysicalGLMatrix H b hb) *ᵥ a)

/-- EXACT equality of this genuine finite Wilson posterior matrix
value and the true full-link GL mass of the ZV/ZW physical tangent. -/
theorem p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37ZX_originalCenteredGLGramValue H b hb =
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  unfold p4Q2PZ37ZX_originalCenteredGLGramValue
  rw [p4Q2PZ37ZW_originalCenteredDirection_eq_static]
  exact p4Q2PZ37ZP_originalStaticPhysicalGLMatrix_quad_eq_GL
    H b hb (p4Q2PZ37ZW_originalCenteredCoefficients H)

/-- A TRUE Wilson spatial direction always contributes a fixed 1/2
coefficient to the centered physical tangent, independent of volume. -/
theorem p4Q2PZ37ZX_originalCenteredCoefficients_norm_sq_ge_quarter
    (H : ℕ) :
    (1 / 4 : ℝ) ≤ ‖p4Q2PZ37ZW_originalCenteredCoefficients H‖^2 := by
  let a := p4Q2PZ37ZW_originalCenteredCoefficients H
  have hCoord : ‖a (1 : Fin 2)‖ ≤ ‖a‖ :=
    norm_le_pi_norm a (1 : Fin 2)
  have hSq : ‖a (1 : Fin 2)‖^2 ≤ ‖a‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hCoord 2
  have hOne : a (1 : Fin 2) = (1 / 2 : ℝ) :=
    p4Q2PZ37ZW_originalCenteredCoefficients_one H
  rw [hOne] at hSq
  norm_num at hSq ⊢
  exact hSq

/-- Any genuinely proved original full-link Wilson 2x2 Gram floor
immediately controls the centered physical source with a fixed
volume-independent coefficient factor 1/4. -/
theorem p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 < m)
    (hFloor : ∀ a : Fin 2 → ℝ,
      m * ‖a‖^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :
    m / 4 ≤
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  let a := p4Q2PZ37ZW_originalCenteredCoefficients H
  have hCoord : (1 / 4 : ℝ) ≤ ‖a‖^2 :=
    p4Q2PZ37ZX_originalCenteredCoefficients_norm_sq_ge_quarter H
  have hFloorA := hFloor a
  rw [p4Q2PZ37ZW_originalCenteredDirection_eq_static]
  calc
    m / 4 = m * (1 / 4 : ℝ) := by ring
    _ ≤ m * ‖a‖^2 := mul_le_mul_of_nonneg_left hCoord hm.le
    _ ≤ p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :=
      hFloorA

/-- The quantitatively positive original GL Gram floor transfers to
the source-normalized genuine Wilson strong fine-zero Rayleigh limit.
The physical norm is NOT replaced by a coefficient norm. -/
theorem p4Q2PZ37ZX_originalCenteredRayleigh_ge_floor_div_physicalNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 < m)
    (hFloor : ∀ a : Fin 2 → ℝ,
      m * ‖a‖^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H b hb.le (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) :
    (m / 4) / ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
      p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
  let V := p4Q2PZ37ZW_originalCenteredPhysicalDirection H
  have hDen : 0 < ‖V‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  have hMass :=
    p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
      H b hb m hm hFloor
  change (m / 4) / ‖V‖^2 ≤
    (p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le V
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))) / ‖V‖^2
  exact (div_le_div_iff₀ hDen hDen).2
    (mul_le_mul_of_nonneg_right hMass hDen.le)

/-- For each fixed genuine finite SU(2) Wilson lattice and positive
frozen coupling, the coefficient floor exists and gives a model-
dependent positive quantitative Rayleigh lower bound at fine zero. -/
theorem p4Q2PZ37ZX_originalCenteredGL_exists_quantitativeRayleighFloor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ m : ℝ, 0 < m ∧
      m / 4 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb ∧
      (m / 4) / ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) := by
  obtain ⟨m, hm, hFloor⟩ :=
    p4Q2PZ37ZP_originalStaticPhysicalGLMass_exists_quadraticFloor
      H b hb e e' left₀ right₀
  refine ⟨m, hm, ?_, ?_⟩
  · rw [p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass]
    exact p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
      H b hb m hm hFloor
  · exact p4Q2PZ37ZX_originalCenteredRayleigh_ge_floor_div_physicalNorm
      H b hb m hm hFloor

/-- The true ZW strict fine-zero Rayleigh limit, expressed EXACTLY
as the original interacting-Wilson-posterior two-source Gram quotient.
This is an equality, not an assumed or approximate matrix frame. -/
theorem p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) =
      p4Q2PZ37ZX_originalCenteredGLGramValue H b hb /
        ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 := by
  unfold p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
  rw [p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass]

/-- Full volume-family criterion: for arbitrary positive frozen Wilson
couplings b_H, uniform centered physical Rayleigh lower bound c is
EQUIVALENT to a genuine weighted two-source Gram condition at every H.
This does NOT assert existence of any c>0 or any common fine interval. -/
theorem p4Q2PZ37ZX_uniformCenteredRayleigh_iff_originalGram
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ) :
    (∀ H : ℕ,
      c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh
        H (b H) (hb H) (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)) ↔
    (∀ H : ℕ,
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) := by
  constructor
  · intro h H
    have hDen : 0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
      pow_pos (norm_pos_iff.mpr
        (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
      at h
    exact (le_div_iff₀ hDen).mp (h H)
  · intro h H
    have hDen : 0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
      pow_pos (norm_pos_iff.mpr
        (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
    rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
    exact (le_div_iff₀ hDen).mpr (h H)

/-- A SHARED positive Gram/frame estimate would imply a shared
positive lower bound of the genuine fixed-H fine-zero Rayleigh limits.
Each individual strict fine-zero convergence is already proved in ZW3;
no uniformity of the convergence rate in H is inferred. -/
theorem p4Q2PZ37ZX_uniformOriginalGram_implies_allFineZeroRayleighLimits
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (c : ℝ) (hc : 0 < c)
    (hGram : ∀ H : ℕ,
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) :
    ∀ H : ℕ,
      c ≤ p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) ∧
      Tendsto (fun t : Set.Ici (0 : ℝ) =>
        p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
          (p4Q2PZ37ZE_originalPhysicalCancellation H t))
        (𝓝[>] (⟨0, le_refl (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
        (𝓝 (p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H (b H) (hb H)
          (p4Q2PZ37ZW_originalCenteredPhysicalDirection H))) := by
  intro H
  exact ⟨(p4Q2PZ37ZX_uniformCenteredRayleigh_iff_originalGram b hb c).2
    hGram H, p4Q2PZ37ZW3_originalPhysicalRayleigh_strictFineZeroLimit
      H (b H) (hb H)⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredCoefficients_norm_sq_ge_quarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredRayleigh_ge_floor_div_physicalNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredGL_exists_quantitativeRayleighFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_uniformCenteredRayleigh_iff_originalGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZX_uniformOriginalGram_implies_allFineZeroRayleighLimits
