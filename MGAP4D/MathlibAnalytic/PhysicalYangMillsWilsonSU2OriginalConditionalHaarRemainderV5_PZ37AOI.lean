import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalLocalRelativeTaylorV5_PZ37AOH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOI — original finite-volume conditional Haar Taylor remainder

Integrate AOH's actual one-link center-twist quadratic remainder against the
ORIGINAL finite spatial-slice product Haar, holding the left boundary A fixed.
The genuine Wilson kernel is in [0,1] for beta >= 0, and the normalized
primary SU(2) character lies in [-1,1]. This gives a volume-independent
64*beta^2 signed-character remainder.

No conditional first-action moment, true-top-state normalized slope, or
volume-uniform normalization of the top Haar amplitude is claimed here.
This leaf does not alter the original Wilson action, Haar law, Gauss Hilbert,
finite-volume geometry, transfer operator, or pinned Lean/mathlib.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOI_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOI_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOI_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOI_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOI_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Original Wilson action/kernels only: the Taylor residual compares the same
right-boundary primary-link center-flipped pair from AOH. -/
noncomputable def p4Q2PZ37AOI_originalRightTwistTaylorRemainder
    (H : ℕ) (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B -
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
    (p4Q2PZ37ANV_singleLinkCenterTwist H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) +
  beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
      (p4Q2PZ37ANV_singleLinkCenterTwist H
        (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)

/-- The original conditional Haar integral of the signed primary-character
relative Taylor residual has an H- and action-budget-independent quadratic
bound for 0 <= beta <= 1/8. The left boundary A is arbitrary and fixed. -/
theorem p4Q2PZ37AOI_originalConditionalHaarRightTwistTaylorRemainder_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 8 * beta ≤ 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |∫ B,
      p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)| ≤
        64 * beta^2 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let chi : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  let kFlip : Cfg → ℝ := fun B =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A (tau B)
  let residual : Cfg → ℝ := fun B =>
    p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hpoint (B : Cfg) : ‖residual B * chi B‖ ≤ 64 * beta^2 := by
    have hResidual : |residual B| ≤ 64 * beta^2 * kFlip B := by
      change |p4Q2PZ37AOI_originalRightTwistTaylorRemainder H beta A B| ≤
        64 * beta^2 *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A (tau B)
      change |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) +
        beta * p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A
            (p4Q2PZ37ANV_singleLinkCenterTwist H
              (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B)| ≤ _
      exact p4Q2PZ37AOH_originalKernel_rightCenterTwist_relativeRemainder_abs_le
        H beta hbeta hsmall A B
    have hKNonneg : 0 ≤ kFlip B := by
      dsimp [kFlip]
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
      exact Real.exp_nonneg _
    have hKLe : kFlip B ≤ 1 := by
      dsimp [kFlip]
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
      apply Real.exp_le_one_iff.mpr
      have hS := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by norm_num) A (tau B)
      nlinarith only [mul_nonneg hbeta hS]
    have hChi : |chi B| ≤ 1 := by
      dsimp [chi]
      rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
      unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
      have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
        (by norm_num : 0 < (2 : ℕ))
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
      have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
        (by norm_num : 0 < (2 : ℕ))
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
      rw [abs_le]
      constructor <;> linarith only [hlow, hup]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |residual B| * |chi B| ≤ (64 * beta^2 * kFlip B) * |chi B| :=
        mul_le_mul_of_nonneg_right hResidual (abs_nonneg _)
      _ ≤ (64 * beta^2 * kFlip B) * 1 :=
        mul_le_mul_of_nonneg_left hChi (mul_nonneg (by positivity) hKNonneg)
      _ ≤ (64 * beta^2) * 1 := by
        have h := mul_le_mul_of_nonneg_left hKLe
          (by positivity : 0 ≤ 64 * beta^2)
        nlinarith only [h]
      _ = 64 * beta^2 := by ring
  change |∫ B, residual B * chi B ∂mu| ≤ 64 * beta^2
  have h :=
    norm_integral_le_of_norm_le_const (μ := mu) (f := fun B => residual B * chi B)
      (C := 64 * beta^2) (Eventually.of_forall hpoint)
  simpa [Real.norm_eq_abs] using h

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOI_originalConditionalHaarRightTwistTaylorRemainder_abs_le
