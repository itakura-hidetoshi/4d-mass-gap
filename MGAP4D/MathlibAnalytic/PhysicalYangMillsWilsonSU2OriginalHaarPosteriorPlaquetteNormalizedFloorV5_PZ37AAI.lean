import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredPhysicalHaarBesselBridgeV5_PZ37AAG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorCertifiedPositiveFineRayleighV5_PZ37AAH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAI — original Haar/source-norm upper meets genuine posterior GL frame

The SAME true original Gauss-law centered physical Wilson source V_H has
its reference product-Haar-L2 norm bounded by 6 P_H (AAG/AAF), where P_H
is the number of ACTUAL spatial Wilson plaquettes, not an invented volume.
The original TWO-interacting-posterior full-link full-pair-Haar GL Gram
(ZP/ZX/ZW) has, at each fixed H and frozen b>0, a genuine positive
two-mode coefficient-frame constant m_(H,b). In the centered direction
its true GL mass is at least m_(H,b)/4. As V_H is nonzero,

  R_(H,b)(V_H) >= m_(H,b) / (24 P_H).

The bound is a TRUE original source-normalized, posterior-dependent
Rayleigh lower bound. It in turn gives an actual finite-volume positive
fine radius via AAE, with c=m/(24 P_H) and R(F_t)>=c/2.

A UNIFORM positive fine-ZERO Rayleigh floor c would follow if one can
prove a family of original posterior two-mode Gram/frame constants
m_H >= 24 c P_H. That extensive posterior lower frame premise is
NOT proved here: it is an explicit SUFFICIENT condition, not necessary.
In particular the upper product-Haar bound is NOT used as a posterior
lower Gram bound. No uniform positive fine interval, endpoint E/F,
H1-H4, continuum mass gap, new axiom or surrogate posterior/source.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAI_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine spatial plaquette index is never empty. This is
witnessed by an ORIGINAL coordinate plaquette, not by a proxy count. -/
theorem p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos (H : ℕ) :
    (0 : ℝ) <
      (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  classical
  have hNat : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
    Fintype.card_pos_iff.mpr
      ⟨pz37zaSpatialPlaquetteCoordinateFamily H 0⟩
  exact_mod_cast hNat

/-- The ZW named PHYSICAL Hilbert tangent is definitionally the
original AAG half-centered Wilson source; its Haar-synthesized upper
bound holds in the ORIGINAL Gauss-law physical Hilbert metric. -/
theorem p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
    (H : ℕ) :
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
      6 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  exact p4Q2PZ37AAG_originalCenteredPhysicalFormulaNorm_sq_le_six_plaquetteCount H

/-- Pure ordered-field step used to distinguish a genuine upper
source norm from an independent lower posterior Gram estimate. -/
private theorem p4Q2PZ37AAI_scaledNorm_le_frameQuarter
    (P m N : ℝ) (hP : 0 < P) (hm : 0 ≤ m)
    (hN : N ≤ 6 * P) :
    (m / (24 * P)) * N ≤ m / 4 := by
  have hCoeff : 0 ≤ m / (24 * P) := div_nonneg hm (by positivity)
  calc
    (m / (24 * P)) * N ≤ (m / (24 * P)) * (6 * P) :=
      mul_le_mul_of_nonneg_left hN hCoeff
    _ = m / 4 := by
      field_simp [ne_of_gt hP]
      <;> ring

/-- A true ORIGINAL interacting-posterior centered two-source Gram
floor m/4 controls the physical source norm at rate m/(24 P_H).
It assumes no positivity of the product-Haar Gram from the posterior. -/
theorem p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 ≤ m)
    (hGram : m / 4 ≤ p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) :
    (m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) *
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb := by
  let P : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  have hP : 0 < P := p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hNorm :
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤ 6 * P :=
    p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H
  exact (p4Q2PZ37AAI_scaledNorm_le_frameQuarter P m
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2
    hP hm hNorm).trans hGram

/-- Concrete full-link true posterior Rayleigh versus actual spatial
plaquette count: this lower bound uses NO Haar replacement. -/
theorem p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 ≤ m)
    (hGram : m / 4 ≤ p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) :
    m / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  have hNorm :
      0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  unfold p4Q2PZ37AAH_originalExactCenteredRayleighFloor
  rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
  exact (le_div_iff₀ hNorm).mpr
    (p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
      H b hb m hm hGram)

/-- At every genuine finite H,b>0, ZP supplies its actual original
posterior two-mode frame constant m>0. With the actual Haar source norm
upper bound this yields a positive quantitative Rayleigh floor
m/(24P_H), and AAE constructs a true positive fine interval with
R(F_t)>=m/(48P_H). The constant remains volume dependent. -/
theorem p4Q2PZ37AAI_originalPosterior_exists_plaquetteScaledFineRadius
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ m : ℝ, 0 < m ∧
      m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb ∧
      0 < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b
        (m / (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) ∧
      ∀ t : Set.Ici (0 : ℝ), 0 < (t : ℝ) →
        (t : ℝ) < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b
          (m / (24 * (Fintype.card
            (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) →
        (m / (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) / 2 ≤
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
            (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  let p := pz37zaSpatialPlaquetteCoordinateFamily H 0
  let e : PeriodicHypercubicEvenSpatialSliceLink H := (p.1, p.2.1.1)
  let A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    fun _ => 1
  obtain ⟨m, hm, hGram, _hRayleigh⟩ :=
    p4Q2PZ37ZX_originalCenteredGL_exists_quantitativeRayleighFloor
      H b hb e e A A
  have hP := p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hc : 0 < m / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) :=
    div_pos hm (by positivity)
  have hSourceGram :=
    p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
      H b hb m hm.le hGram
  have hFine :=
    p4Q2PZ37AAE_originalCertifiedRadius_positiveRayleighFloor
      H b hb
      (m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)))
      hc hSourceGram
  refine ⟨m, hm, ?_, hFine.1, ?_⟩
  · exact p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
      H b hb m hm.le hGram
  · intro t ht htρ
    exact (hFine.2 t ht htρ).2

/-- Entirely original *sufficient* all-volume criterion.
An extensive lower bound m_H >= 24*c*P_H for genuine full-link,
two-Wilson-posterior physical coefficient-frames would produce a
common fine-ZERO centered physical Rayleigh floor c>0. Existence
of such m_H is NOT asserted, nor does this provide a common fine
interval: AAB/AAD's global budget obstruction remains untouched. -/
theorem p4Q2PZ37AAI_uniformCenteredFineZeroFloor_of_extensivePosteriorFrame
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (m : ℕ → ℝ) (hm : ∀ H, 0 < m H)
    (c : ℝ) (hc : 0 < c)
    (hFrame : ∀ H : ℕ, ∀ a : Fin 2 → ℝ,
      m H * ‖a‖^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H (b H) (hb H).le
          (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
    (hExtensive : ∀ H : ℕ,
      24 * c * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ≤ m H) :
    ∀ H : ℕ, 0 < c ∧
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  intro H
  have hP : 0 < (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) :=
    p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hDen : 0 < 24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
    positivity
  have hRatio : c ≤ m H / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) := by
    apply (le_div_iff₀ hDen).mpr
    calc
      c * (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) =
        24 * c * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by ring
      _ ≤ m H := hExtensive H
  have hGram : m H / 4 ≤
      p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H) := by
    rw [p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass]
    exact p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
      H (b H) (hb H) (m H) (hm H) (hFrame H)
  exact ⟨hc, hRatio.trans
    (p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
      H (b H) (hb H) (m H) (hm H).le hGram)⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalPosterior_exists_plaquetteScaledFineRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_uniformCenteredFineZeroFloor_of_extensivePosteriorFrame
