import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarEvenLaplaceV5_PZ37ALB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALC — genuine original crossing-weighted pair-Haar source moments

The already-authenticated ALA diagonal center transformation preserves the
ACTUAL two-endpoint SU(2) product Haar and the original crossing kernel,
while reversing the ORIGINAL centered physical pair-source sum.
ALB proves the exact genuine pair-Haar Laplace integral is even.

This append-only leaf descends the symmetry to the zero FIRST moment and
then retains the ACTUAL nonnegative SECOND crossing-weighted Haar moment.
A global elementary exp inequality supplies a quantitative quadratic
lower bound for the unchanged true pair Laplace transform, at any H.

In particular the quadratic lower term has the exact original
pair-source squared integrand; it is not a Gaussian assumption, a
different Wilson transfer, or a replacement Haar probability law.

NO value or positive numerical lower bound is asserted for the second
moment; NO H22 negative-region upper Haar mass r22, AJA witness verdict,
Hamiltonian gap or continuum mass gap is claimed. The H22 obstruction
identified in AKX/AKY/AKZ remains open. Existing original physical
definitions, prior files, pinned toolchain and canonical root unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALC_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- A fully global real-variable estimate. For either sign of x,
combine the pinned nonnegative quadratic exponential floor with
the opposite-sign exponential tangent. The 1/4 coefficient is
deliberately conservative and uses no assumed moment estimate. -/
theorem p4Q2PZ37ALC_real_expSymm_ge_quadratic (x : ℝ) :
    1 + x ^ 2 / 4 ≤ (Real.exp x + Real.exp (-x)) / 2 := by
  rcases le_total 0 x with hx | hx
  · have hQuadratic := Real.quadratic_le_exp_of_nonneg hx
    have hTangent := Real.add_one_le_exp (-x)
    nlinarith only [hQuadratic, hTangent]
  · have hQuadratic := Real.quadratic_le_exp_of_nonneg (neg_nonneg.mpr hx)
    have hTangent := Real.add_one_le_exp x
    nlinarith only [hQuadratic, hTangent]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "T" => p4Q2PZ37AHW_originalCenterTwist H
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Lpair" => p4Q2PZ37ALB_originalPairCrossingLaplace H

/-- Integrability of the ACTUAL original crossing-weighted signed
pair source, before invoking diagonal center-Haar symmetry. -/
theorem p4Q2PZ37ALC_originalPairCrossingFirstMoment_integrable (beta : ℝ) :
    Integrable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 * (fCont P.1 + fCont P.2)) pairH := by
  have hKC : Continuous (fun P : Cfg × Cfg => KC beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
      H 2 beta
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact (hKC.mul (hf1.add hf2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The first crossing-weighted ORIGINAL pair-source Haar moment
vanishes EXACTLY. This uses the proved product MeasurePreserving
map; the cancellation is not inferred from a formal odd integrand
without checking the Haar pushforward. -/
theorem p4Q2PZ37ALC_originalPairCrossingFirstMoment_zero (beta : ℝ) :
    (∫ P : Cfg × Cfg,
      KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ∂pairH) = 0 := by
  let M : Cfg × Cfg → Cfg × Cfg := Prod.map T T
  have hPres : MeasurePreserving M pairH pairH :=
    p4Q2PZ37ALA_originalPairHaar_diagonalCenter_preserving H
  have hMap : Measure.map M pairH = pairH := hPres.map_eq
  have hIntegrable :=
    p4Q2PZ37ALC_originalPairCrossingFirstMoment_integrable H beta
  have hAEStrong : AEStronglyMeasurable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 * (fCont P.1 + fCont P.2)) (Measure.map M pairH) := by
    rw [hMap]
    exact hIntegrable.aestronglyMeasurable
  have hOdd :
      (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ∂pairH) =
      (∫ P : Cfg × Cfg,
        -(KC beta P.1 P.2 * (fCont P.1 + fCont P.2)) ∂pairH) := by
    calc
      _ = ∫ P : Cfg × Cfg,
        KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ∂Measure.map M pairH := by
          rw [hMap]
      _ = ∫ P : Cfg × Cfg,
        KC beta (T P.1) (T P.2) *
          (fCont (T P.1) + fCont (T P.2)) ∂pairH := by
          exact MeasureTheory.integral_map hPres.measurable.aemeasurable hAEStrong
      _ = ∫ P : Cfg × Cfg,
        -(KC beta P.1 P.2 * (fCont P.1 + fCont P.2)) ∂pairH := by
          apply integral_congr_ae
          filter_upwards with P
          exact p4Q2PZ37ALA_originalPairCrossingSource_diagonalCenter_odd
            H beta P.1 P.2
  rw [integral_neg] at hOdd
  linarith only [hOdd]

/-- Derived true SU(2) crossing-weighted second moment; the original
Haar law, original crossing kernel, original ZW source are retained. -/
def p4Q2PZ37ALC_originalPairCrossingSecondMoment (beta : ℝ) : ℝ :=
  ∫ P : Cfg × Cfg,
    KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2 ∂pairH

local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H

theorem p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable (beta : ℝ) :
    Integrable (fun P : Cfg × Cfg =>
      KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) pairH := by
  have hKC : Continuous (fun P : Cfg × Cfg => KC beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
      H 2 beta
  have hf1 : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hf2 : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  exact (hKC.mul ((hf1.add hf2).pow 2)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- An unconditional nonnegative exact physical second moment, with
NO asserted numerical positive lower bound. -/
theorem p4Q2PZ37ALC_originalPairCrossingSecondMoment_nonneg (beta : ℝ) :
    0 ≤ M2pair beta := by
  unfold p4Q2PZ37ALC_originalPairCrossingSecondMoment
  apply integral_nonneg
  intro P
  exact mul_nonneg
    (p4Q2PZ37AIN_originalCrossingKernel_pos H beta P.1 P.2).le
    (sq_nonneg _)

/-- The actual pair-Laplace integral has a certified quadratic lower
term built from the true original crossing-weighted pair-source square.
No independence or Gaussian approximation is used. -/
theorem p4Q2PZ37ALC_originalPairLaplace_quadraticMoment_lower
    (beta t : ℝ) :
    Zcross beta + (t ^ 2 / 4) * M2pair beta ≤ Lpair beta t := by
  have hKCInt := p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H beta
  have hM2Int :=
    p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable H beta
  have hPlus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta t
  have hMinus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta (-t)
  have hLowerInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 +
          (t ^ 2 / 4) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2)) pairH :=
    hKCInt.add (hM2Int.const_mul (t ^ 2 / 4))
  have hSymInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2)) pairH := by
    have hI := (hPlus.add hMinus).const_mul (1 / 2 : ℝ)
    convert hI using 1
    ext P
    ring
  have hPointwise (P : Cfg × Cfg) :
      KC beta P.1 P.2 +
          (t ^ 2 / 4) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ≤
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) := by
    let s : ℝ := fCont P.1 + fCont P.2
    have hKC : 0 ≤ KC beta P.1 P.2 :=
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta P.1 P.2).le
    have hExp :
        1 + (t * s) ^ 2 / 4 ≤
          (Real.exp (t * s) + Real.exp ((-t) * s)) / 2 := by
      simpa only [neg_mul] using
        p4Q2PZ37ALC_real_expSymm_ge_quadratic (t * s)
    calc
      _ = KC beta P.1 P.2 * (1 + (t * s) ^ 2 / 4) := by
        dsimp [s]
        ring
      _ ≤ KC beta P.1 P.2 *
          ((Real.exp (t * s) + Real.exp ((-t) * s)) / 2) :=
        mul_le_mul_of_nonneg_left hExp hKC
      _ = _ := by rfl
  have hLowerValue :
      (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 +
          (t ^ 2 / 4) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ∂pairH) =
      Zcross beta + (t ^ 2 / 4) * M2pair beta := by
    rw [integral_add hKCInt (hM2Int.const_mul (t ^ 2 / 4)),
      integral_const_mul,
      p4Q2PZ37AIV_originalCrossingKernel_pair_integral H beta]
    rfl
  calc
    Zcross beta + (t ^ 2 / 4) * M2pair beta =
        (∫ P : Cfg × Cfg,
          KC beta P.1 P.2 +
            (t ^ 2 / 4) *
              (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ∂pairH) :=
        hLowerValue.symm
    _ ≤ (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) ∂pairH) :=
      integral_mono hLowerInt hSymInt hPointwise
    _ = Lpair beta t :=
      (p4Q2PZ37ALB_originalPairLaplace_symmetrized H beta t).symm

/-- Remove only the certified nonnegative quadratic correction. -/
theorem p4Q2PZ37ALC_originalPairLaplace_ge_crossingPartition
    (beta t : ℝ) :
    Zcross beta ≤ Lpair beta t := by
  have hm := p4Q2PZ37ALC_originalPairCrossingSecondMoment_nonneg H beta
  have ht : 0 ≤ (t ^ 2 / 4 : ℝ) := by positivity
  have hExtra : 0 ≤ (t ^ 2 / 4) * M2pair beta := mul_nonneg ht hm
  have hBound := p4Q2PZ37ALC_originalPairLaplace_quadraticMoment_lower H beta t
  linarith only [hExtra, hBound]

/-- An exact H22 specialization of the original-model quadratic
certificate. The needed H22 negative Haar-mass upper bound is separate. -/
theorem p4Q2PZ37ALC_originalH22_pairLaplace_quadraticMoment_lower
    (beta t : ℝ) :
    p4Q2PZ37AIF_originalCrossingPartition 22 beta +
      (t ^ 2 / 4) *
        p4Q2PZ37ALC_originalPairCrossingSecondMoment 22 beta ≤
      p4Q2PZ37ALB_originalPairCrossingLaplace 22 beta t :=
  p4Q2PZ37ALC_originalPairLaplace_quadraticMoment_lower 22 beta t

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ALC_real_expSymm_ge_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairCrossingFirstMoment_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairCrossingFirstMoment_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairCrossingSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairCrossingSecondMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairLaplace_quadraticMoment_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalPairLaplace_ge_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALC_originalH22_pairLaplace_quadraticMoment_lower
