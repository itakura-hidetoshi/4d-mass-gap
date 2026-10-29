import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIOpenPairHaarEventV5_PZ37ABB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABB2 — genuine source-projection moment, two-sided Wilson bounds

The ORIGINAL two-interacting-Wilson-posterior physical expectation gap
has the exact model-specific factorization (GI):
   Delta_(H,b,e)(z) = alpha_(H,b,e,V_H)(z) * Q_(H,b,e)(z).
Here alpha is GB's actual centered Gauss-law source/contrast Haar
projection, Q is FX's actual strictly positive normalized Wilson
posterior contrast Haar-L² variance, with unchanged outer pair-Haar.

GA proves a volume-independent positive lower bound for Q at any
frozen b>0, and ABA freshly proves an independent upper bound from
FK, with ONLY standard axioms. GD proves alpha² integrability;
ABA/AAZ2 prove Delta² integrability.

Consequently the unweighted true GI moment G is TWO-SIDED comparable
with the original physical source-projection Haar second moment A:
  c_b² A <= G <= C_b² A,
  c_b = exp(-32b) * b² * V_SU2 > 0,
  C_b = (exp(16b)-exp(-16b))² > 0.
Both constants are independent of spatial H, actual link e and
outer boundary configuration (at fixed b).

In particular there exists a genuine spatial link with A>0 for
EVERY finite H,b>0, unconditionally. This identifies an exact,
source-dependent noncancellation obstruction to uniform G: the
density-contrast Q cannot itself degenerate at fixed positive b,
whereas alpha_H may have vanishing volume infimum.

No UNCONDITIONAL H-independent positive A floor is proved; this is
NOT a continuum mass gap, all-physical-source coercivity, or a
volume-uniform real cylinder. No new axiom/sorry/admit/native_decide,
no changed Wilson kernel, positive Perron vacuum, source, conditional
posterior or pair-Haar, no Dobrushin, E/F, H1-H4 or fine interval.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABB2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABB2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABB2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABB2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABB2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Exact original pair-Haar L² squared moment of the GB original
centered physical-source projection onto the difference of the
two actually interacting Wilson conditional density rows. -/
noncomputable def p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ z,
    (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Exact pointwise factorization of the unchanged ORIGINAL physical
GI expectation gap squared into GB projection squared times true FX
posterior-density contrast variance squared. -/
theorem p4Q2PZ37ABB2_originalGIGapSquare_eq_projectionSq_mul_trueFXSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 =
    (p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 *
      (p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H b hb.le z.2 e)^2 := by
  rw [p4Q2GI_originalWilsonSignedExpectationGap_eq_projection_mul_variance
    H b hb (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z]
  ring

/-- Two-sided comparison of full-pair-Haar unweighted original GI
squared moment G and the original source-projection squared moment A.
The positive coefficient c_b and upper coefficient C_b are entirely
independent of H and of the real spatial link. -/
theorem p4Q2PZ37ABB2_originalUnweightedGI_vs_projectionMoment_twoSided
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Real.exp (-32 * b) *
      (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance))^2 *
        p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment H b hb e ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e ∧
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e ≤
      ((Real.exp (16 * b) - Real.exp (-16 * b))^2)^2 *
        p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment H b hb e := by
  let Pair :=
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let A : Pair → ℝ := fun z =>
    p4Q2GB_originalPhysicalSourcePosteriorContrastProjection
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let D : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let Q : Pair → ℝ := fun z =>
    p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H b hb.le z.2 e
  let c : ℝ := Real.exp (-32 * b) *
    (b^2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance)
  let C : ℝ := (Real.exp (16 * b) - Real.exp (-16 * b))^2
  have hc : 0 < c :=
    mul_pos (Real.exp_pos _)
      (mul_pos (pow_pos hb 2)
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos)
  have hAInt : Integrable (fun z : Pair => (A z)^2) μ := by
    exact p4Q2GD_originalPhysicalSourceProjection_sq_integrable
      H b hb (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e
  have hQCap : ∀ z : Pair, Q z ≤ C := by
    intro z
    exact p4Q2PZ37ABA_originalFXVariance_le_FK_envelope H b hb.le z.2 e
  have hDInt : Integrable (fun z : Pair => (D z)^2) μ := by
    exact p4Q2PZ37AAZ2_originalUnweightedGIGapSquare_integrable_of_FXCap
      H b hb e C hQCap
  have hPoint (z : Pair) :
      c^2 * (A z)^2 ≤ (D z)^2 ∧
      (D z)^2 ≤ C^2 * (A z)^2 := by
    have hQlo : c ≤ Q z :=
      p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
        H b hb.le z.2 e
    have hQpos : 0 < Q z :=
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
        H b hb z.2 e
    have hLoSq : c^2 ≤ (Q z)^2 :=
      pow_le_pow_left₀ hc.le hQlo 2
    have hHiSq : (Q z)^2 ≤ C^2 :=
      pow_le_pow_left₀ hQpos.le (hQCap z) 2
    have hFact : (D z)^2 = (A z)^2 * (Q z)^2 :=
      p4Q2PZ37ABB2_originalGIGapSquare_eq_projectionSq_mul_trueFXSq
        H b hb e z
    constructor
    · calc
        c^2 * (A z)^2 ≤ (Q z)^2 * (A z)^2 :=
          mul_le_mul_of_nonneg_right hLoSq (sq_nonneg _)
        _ = (D z)^2 := by rw [hFact]; ring
    · calc
        (D z)^2 = (Q z)^2 * (A z)^2 := by rw [hFact]; ring
        _ ≤ C^2 * (A z)^2 :=
          mul_le_mul_of_nonneg_right hHiSq (sq_nonneg _)
  change
    c^2 * (∫ z, (A z)^2 ∂μ) ≤ (∫ z, (D z)^2 ∂μ) ∧
      (∫ z, (D z)^2 ∂μ) ≤ C^2 * (∫ z, (A z)^2 ∂μ)
  constructor
  · calc
      c^2 * (∫ z, (A z)^2 ∂μ) =
          ∫ z, c^2 * (A z)^2 ∂μ := by rw [integral_const_mul]
      _ ≤ ∫ z, (D z)^2 ∂μ := by
        apply integral_mono (hAInt.const_mul (c^2)) hDInt
        intro z
        exact (hPoint z).1
  · calc
      (∫ z, (D z)^2 ∂μ) ≤
          ∫ z, C^2 * (A z)^2 ∂μ := by
        apply integral_mono hDInt (hAInt.const_mul (C^2))
        intro z
        exact (hPoint z).2
      _ = C^2 * (∫ z, (A z)^2 ∂μ) := by rw [integral_const_mul]

/-- The unchanged physical source has strictly positive ORIGINAL
pair-Haar projection-square moment at some genuine link for every
finite H,b>0. This is unconditional but not a uniform-in-H bound. -/
theorem p4Q2PZ37ABB2_exists_originalLink_positivePhysicalProjectionMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment H b hb e := by
  obtain ⟨e, hG⟩ :=
    p4Q2PZ37ABA2_exists_originalLink_positiveUnweightedGIMoment H b hb
  refine ⟨e, ?_⟩
  have hHi :=
    (p4Q2PZ37ABB2_originalUnweightedGI_vs_projectionMoment_twoSided
      H b hb e).2
  have hNonneg :
      0 ≤ ((Real.exp (16 * b) - Real.exp (-16 * b))^2)^2 :=
    sq_nonneg _
  by_contra hn
  have hAle :
      p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment H b hb e ≤ 0 :=
    le_of_not_gt hn
  have hProd :
      ((Real.exp (16 * b) - Real.exp (-16 * b))^2)^2 *
        p4Q2PZ37ABB2_originalCenteredPhysicalProjectionMoment H b hb e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hNonneg hAle
  exact (not_le_of_gt hG) (hHi.trans hProd)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABB2_originalGIGapSquare_eq_projectionSq_mul_trueFXSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABB2_originalUnweightedGI_vs_projectionMoment_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABB2_exists_originalLink_positivePhysicalProjectionMoment
