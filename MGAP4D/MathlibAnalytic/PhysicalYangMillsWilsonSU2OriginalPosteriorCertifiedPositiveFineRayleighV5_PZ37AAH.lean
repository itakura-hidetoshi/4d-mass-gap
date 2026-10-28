import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExplicitPositiveFineRadiusV5_PZ37AAE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAH — genuine posterior Gram floor certifies fixed-volume fine Rayleigh

PZ37ZW established strict positivity of the ACTUAL full-spatial-link,
complete boundary pair-Haar, TWO-interacting-Wilson-posterior GL mass
on the genuine nonzero centered physical Wilson tangent at each finite
volume H and frozen b>0. ZX identifies this mass with the exact
original two-mode Gram value. AAE then constructed a positive fine
radius from any certified positive Gram floor c.

Here there is NO EXTERNAL Gram-floor hypothesis: choose c_(H,b)
to be the ACTUAL original source-normalized centered GL Gram/Rayleigh
value itself. The original ZW positivity gives c_(H,b)>0, and ZX
identifies c_(H,b)*||V_H||^2 exactly with the original posterior Gram.
AAE therefore gives an unconditional, explicitly defined positive
fine radius at each fixed H and b>0.

This does not give a computable uniform numerical floor; c_(H,b)
still depends on the exact original interacting posterior Gram and
source norm. It asserts no all-volume common interval, E/F, H1-H4,
or 4D continuum mass gap. AAG's independent original Haar synthesis
upper bound remains separate: Haar covariance is not posterior
coercivity. No new axiom or substitute physical source.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAH_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A concrete ORIGINAL spatial-slice link suffices for the old
all-link positive-mass theorem; no new finite-volume witness
assumption or arbitrary configuration choice is needed. -/
private def p4Q2PZ37AAH_originalCanonicalLink
    (H : ℕ) : PeriodicHypercubicEvenSpatialSliceLink H :=
  let p := pz37zaSpatialPlaquetteCoordinateFamily H 0
  (p.1, p.2.1.1)

/-- The actual normalized interacting-posterior GL Rayleigh value
on the original centered Gauss-law physical Wilson direction. -/
noncomputable def p4Q2PZ37AAH_originalExactCenteredRayleighFloor
    (H : ℕ) (b : ℝ) (hb : 0 < b) : ℝ :=
  p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
    (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

/-- No external Gram lower-bound assumption: true posterior detection
and the original nonconstant Wilson source prove strict positivity. -/
theorem p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  let e := p4Q2PZ37AAH_originalCanonicalLink H
  let A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    fun _ => 1
  exact p4Q2PZ37ZW_originalCenteredDirection_Rayleigh_pos
    H b hb e e A A

/-- The chosen positive floor is exactly the genuine centered
original two-posterior Gram divided by physical source norm squared.
This is not a reference Haar Gram substitution. -/
theorem p4Q2PZ37AAH_originalExactCenteredRayleighFloor_mul_norm_sq_eq_gram
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb *
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 =
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb := by
  unfold p4Q2PZ37AAH_originalExactCenteredRayleighFloor
  rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
  have hNorm : ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≠ 0 :=
    ne_of_gt (pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2)
  exact div_mul_cancel₀
    (p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) hNorm

/-- The concrete original AAE certified radius, with c chosen from
the exact ORIGINAL centered Wilson interacting-posterior Gram. -/
noncomputable def p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius
    (H : ℕ) (b : ℝ) (hb : 0 < b) : ℝ :=
  p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b
    (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)

/-- Unconditional at EVERY fixed finite H and frozen b>0: original
full-link physical cancellation Rayleigh remains strictly positive
on this explicitly constructed original-posterior-dependent fine
interval. There is no volume-independent or continuum assertion. -/
theorem p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius_positiveRayleigh
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius H b hb ∧
      ∀ t : Set.Ici (0 : ℝ),
        0 < (t : ℝ) →
        (t : ℝ) < p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius H b hb →
        0 < p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb / 2 ∧
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb / 2 ≤
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
            (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  unfold p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius
  exact p4Q2PZ37AAE_originalCertifiedRadius_positiveRayleighFloor
    H b hb
    (p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb)
    (p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos H b hb)
    (le_of_eq
      (p4Q2PZ37AAH_originalExactCenteredRayleighFloor_mul_norm_sq_eq_gram
        H b hb))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAH_originalExactCenteredRayleighFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAH_originalExactCenteredRayleighFloor_mul_norm_sq_eq_gram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAH_originalPosteriorCertifiedFineRadius_positiveRayleigh
