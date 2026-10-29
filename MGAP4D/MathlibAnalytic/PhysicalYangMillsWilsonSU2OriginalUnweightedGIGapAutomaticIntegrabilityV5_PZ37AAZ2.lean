import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnweightedGIGapMomentCriterionV5_PZ37AAZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAZ2 — automatic unweighted GI-gap integrability from TRUE FX cap

AAZ's unweighted original GI squared moment comparison had a separate
integrability premise for the same genuine two-interacting-Wilson-posterior
centered physical expectation gap. This file ELIMINATES that extra premise
whenever the (still UNSOLVED uniformly) genuine FX variance upper bound
Q_(H,b,e,z) <= q holds.

This follows from the exact ORIGINAL signal identity D^2=(D^2/Q)*Q,
strictly positive true FX variance, AAX's PROVED integrability of the
genuine pair-Haar signal, and GD's original posterior-contrast variance
measurability. GD's measurability theorem is checked to depend only on
propext, Classical.choice, Quot.sound; do NOT import JL's five inherited
native_decide axioms. No source, posterior or measure substitution.

Hence the all-volume criterion for a common Rayleigh m/(18q)>0
requires ONLY a genuine positive lower bound m on the UNWEIGHTED
pair-Haar GI gap-square moment of ONE actual link and a positive
upper bound q on the TRUE FX posterior variance, with no independent
integrability or artificial Rayleigh assumptions.

Neither uniform m nor uniform q is asserted unconditionally.
Append-only, no sorry/admit/native_decide, common fine interval,
endpoint E/F, H1-H4, or continuum Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAZ2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAZ2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAZ2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAZ2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAZ2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- No separate integrability premise for the genuine UNWEIGHTED centered
GI expectation gap is needed once a pointwise bound for its actual
positive FX posterior denominator is available. The input Q upper
bound is explicit, while the actual AAX pair-Haar signal integrability
and GD genuine posterior variance measurability are unconditional. -/
theorem p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (q : ℝ) (hq : 0 < q)
    (hQcap : ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q) :
    Integrable
      (fun z =>
        (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let Q : Pair → ℝ := fun z =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb.le z.2 e
  let S : Pair → ℝ := p4Q2PZ37AAX_originalCenteredPosteriorSignal H b hb e
  have hSInt : Integrable S μ :=
    p4Q2PZ37AAX_originalCenteredPosteriorSignal_integrable H b hb e
  have hQM : Measurable Q :=
    (p4Q2GD_originalWilsonPosteriorContrastHaarSq_measurable
      H b hb.le e).comp measurable_snd
  have hProdM : AEStronglyMeasurable (fun z : Pair => S z * Q z) μ :=
    hSInt.aestronglyMeasurable.mul hQM.aestronglyMeasurable
  have hEq (z : Pair) : (D z)^2 = S z * Q z := by
    have hQpos : 0 < Q z :=
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
        H b hb z.2 e
    change (D z)^2 = ((D z)^2 / Q z) * Q z
    exact (div_mul_cancel₀ ((D z)^2) hQpos.ne').symm
  have hGapM : AEStronglyMeasurable (fun z : Pair => (D z)^2) μ := by
    have hFn :
        (fun z : Pair => (D z)^2) = (fun z : Pair => S z * Q z) := by
      funext z
      exact hEq z
    rw [hFn]
    exact hProdM
  have hBound (z : Pair) :
      ‖(D z)^2‖ ≤ ‖q * S z‖ := by
    have hS : 0 ≤ S z :=
      p4Q2PZ37AAX_originalCenteredPosteriorSignal_nonneg H b hb e z
    have hGap :
        (D z)^2 ≤ q * S z :=
      p4Q2PZ37AAZ_originalGapSquare_le_FXCap_mul_trueSignal
        H b hb e z q (hQcap z)
    calc
      ‖(D z)^2‖ = (D z)^2 :=
        Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ q * S z := hGap
      _ = ‖q * S z‖ :=
        (Real.norm_of_nonneg (mul_nonneg hq.le hS)).symm
  change Integrable (fun z : Pair => (D z)^2) μ
  apply Integrable.mono' (hSInt.const_mul q) hGapM
  filter_upwards with z
  exact hBound z

/-- An actual FX upper cap automatically makes the UNWEIGHTED
GI-gap moment integrable; hence the AAZ comparison requires no
extra analytic premise beyond the variance cap itself. -/
theorem p4Q2PZ37AAZ2_originalGapMoment_le_FXCap_mul_raw_noIntegrability
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (q : ℝ) (hq : 0 < q)
    (hQcap : ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e ≤ q) :
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e ≤
      q * p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e := by
  exact p4Q2PZ37AAZ_originalGapMoment_le_FXCap_mul_rawResponse
    H b hb e q hQcap
    (p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
      H b hb e q hq hQcap)

/-- New tight all-volume criterion, with NO independent integrability
assumption: a genuine positive unweighted two-Wilson-posterior GI-gap
second moment m on one original spatial link in every volume and a
uniform positive FX variance cap q suffice for physical Rayleigh
R_H >= m/(18q). Both quantitative bounds remain unproved. -/
theorem p4Q2PZ37AAZ2_allVolumes_Rayleigh_of_unweightedGIMoments
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (m q : ℝ) (hm : 0 < m) (hq : 0 < q)
    (e : ∀ H, PeriodicHypercubicEvenSpatialSliceLink H)
    (hQcap : ∀ H, ∀ z,
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H (b H) (hb H).le z.2 (e H) ≤ q)
    (hMoment : ∀ H,
      m ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
        H (b H) (hb H) (e H)) :
    0 < (m / q) / 18 ∧
      ∀ H, (m / q) / 18 ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  exact p4Q2PZ37AAZ_allVolumes_Rayleigh_of_trueUnweightedGIMoments
    b hb m q hm hq e hQcap
    (fun H =>
      p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
        H (b H) (hb H) (e H) q hq (hQcap H))
    hMoment

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ2_originalGapMoment_le_FXCap_mul_raw_noIntegrability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAZ2_allVolumes_Rayleigh_of_unweightedGIMoments