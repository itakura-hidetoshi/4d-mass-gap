import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStaticTwoModeGISOSFloorV5_PZ37ZL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIJointBoundaryContinuityV5_HI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZM — original full-link GL detection nullity on ALL physical sources

For EVERY actual original SU(2) Wilson Gauss-law physical Hilbert
source, not just a finite right-Krylov combination, and every frozen
coupling b>0, the true all-link, complete pair-Haar integrated GL
posterior gap-square mass vanishes IFF ALL original two-interacting-
posterior GI expectation gaps vanish at EVERY genuine physical
boundary context.

The proof uses GM's existing exact positive-variance weighted-integral
null criterion, HI's previously proved continuous ORIGINAL GI detector
for every physical source, and genuine pair-Haar full topological
support. It never attributes positive Haar mass to a single point:
an actual nonzero point GI witness is extended by continuity before
using the original Haar integral. Consequently any single nonzero
genuine contextual GI detection yields strictly positive ORIGINAL
full-link GL mass, without an assumed frame/rank hypothesis.

This is the analytic point-to-integral bridge toward the PZ37ZL
physical fine-quadratic mass lower bound. It does not yet give a
fine-uniform quantitative GL mass floor, nonphysical source,
independent-Haar posterior, new axiom, sorry, admit, native_decide,
volume/depth-uniform frame, E/F, H1-H4, or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZM_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ZM_su2Haar :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsHaarMeasure := by
  dsimp [normalizedCompactHaar]
  infer_instance

local instance p4Q2PZ37ZM_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance p4Q2PZ37ZM_pairHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- For an arbitrary genuine physical source, the unchanged positive
frozen two-Wilson-posterior all-link Haar-integral GL mass vanishes
precisely when its genuine GI expectation gap vanishes at every
individual actual link and full pair-boundary context. -/
theorem p4Q2PZ37ZM_originalFullLinkGLMass_zero_iff_allOriginalGI
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) = 0 ↔
    ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ∀ z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f e z = 0 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let Pair := Cfg × Cfg
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  have hNull :=
    p4Q2GM_originalWilsonGapSquarePatch_zero_iff_allLinks_gapAE
      H b hb f (Finset.univ : Finset Link)
  constructor
  · intro hZero e z
    have hAE :
        ∀ᵐ y : Pair ∂μ,
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le f e y = 0 :=
      hNull.mp hZero e (Finset.mem_univ e)
    have hContinuous :=
      p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le f e
    have hEq :
        (fun y : Pair =>
          p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb.le f e y) = (fun _ : Pair => (0 : ℝ)) :=
      MeasureTheory.Measure.eq_of_ae_eq hAE hContinuous continuous_const
    exact congrFun hEq z
  · intro hAll
    apply hNull.mpr
    intro e _he
    filter_upwards with z
    exact hAll e z

/-- Unconditional true-Wilson point-to-Haar-GL positivity for ALL
Gauss-law physical sources: one genuine pointwise GI witness implies
positive mass on an open positive-measure Haar region, hence the full
original link-integrated GL mass is strictly positive. -/
theorem p4Q2PZ37ZM_originalFullLinkGLMass_pos_of_originalGI_point
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (hGI :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le f e z ≠ 0) :
    0 < p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
      H b hb.le f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) := by
  have hNonneg :=
    p4Q2GM_originalWilsonGapSquarePatch_nonneg H b hb f
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hNe :
      p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
        H b hb.le f
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) ≠ 0 := by
    intro hZero
    exact hGI
      ((p4Q2PZ37ZM_originalFullLinkGLMass_zero_iff_allOriginalGI
        H b hb f).mp hZero e z)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZM_originalFullLinkGLMass_zero_iff_allOriginalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZM_originalFullLinkGLMass_pos_of_originalGI_point
