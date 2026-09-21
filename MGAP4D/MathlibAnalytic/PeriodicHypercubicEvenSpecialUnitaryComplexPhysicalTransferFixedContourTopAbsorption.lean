import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferRieszProjectorBetaContinuity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferCFCResolventTopPole
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-!
# Fixed-contour top-sector absorption under Wilson-coupling perturbation

Fix a nonnegative coupling beta0 and the canonical Riesz circle chosen there.
The preceding contour-persistence theorem says that this same circle remains in
the resolvent set for all sufficiently nearby beta.  This file proves that the
corresponding fixed-contour Riesz continuation absorbs the *actual* canonical
CFC top sector at the nearby beta on both sides.

The proof is deliberately local and algebraic:

* the nearby canonical top projection is fixed on both sides by the normalized
  transfer operator;
* the general resolvent residue identities therefore hold at every point of
  the fixed beta0 circle once contour persistence supplies resolvent
  membership;
* the exact pole term is integrated around the circle;
* fixed left/right multiplication is moved through the Banach-valued circle
  integral using a continuous linear map.

No continuity of the excited-sector gap is used, and no identification of the
fixed-contour projector with the nearby canonical CFC projector is asserted
here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology Metric
open scoped InnerProductSpace Ring Topology Interval Real

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

local instance fixedContourTopAbsorptionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fixedContourTopAbsorptionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fixedContourTopAbsorptionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fixedContourTopAbsorptionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedContourTopAbsorptionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fixedContourTopAbsorptionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedContourTopAbsorptionRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance fixedContourTopAbsorptionComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- For beta sufficiently near beta0, the fixed beta0 Riesz-contour
continuation absorbs the actual nearby canonical CFC top projection on both
sides.

This uses only persistence of the fixed contour in the resolvent set and the
exact algebraic residue of the nearby canonical fixed sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector_eventually_absorbs_cfcTopProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta0 : Set.Ici (0 : ℝ)) :
    ∀ᶠ beta in 𝓝 beta0,
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta *
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 ∧
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 *
        periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_fixedCanonicalRieszProjector
          H N hN beta0 beta =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta.1 beta.2 := by
  let E := PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N
  let A := E →L[ℂ] E
  let S :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperatorHalfLine
      H N hN
  let r :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius
      H N hN beta0.1 beta0.2
  have hr : 0 < r := by
    simpa [r] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCRieszRadius_pos
        H N hN beta0.1 beta0.2
  have hresEvent :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_canonicalRieszCircle_eventually_subset_resolventSet
      H N hN beta0
  have hcontEvent :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_resolvent_continuousOn_canonicalRieszCircle_eventually_beta
      H N hN beta0
  filter_upwards [hresEvent, hcontEvent] with beta hres hcont
  let P : A :=
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta.1 beta.2
  have hSP : S beta * P = P := by
    simpa [S, P] using
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection
        H N hN beta.1 beta.2
  have hPS : P * S beta = P := by
    simpa [S, P] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator
        H N hN beta.1 beta.2
  have hresIntegrable :
      CircleIntegrable (fun z : ℂ => resolvent (S beta) z) (1 : ℂ) r :=
    hcont.circleIntegrable hr.le
  have hSphereNe :
      ∀ z ∈ Metric.sphere (1 : ℂ) r, z ≠ (1 : ℂ) := by
    intro z hz hzeq
    subst z
    rw [Metric.mem_sphere] at hz
    have hzero : (0 : ℝ) = r := by
      simpa using hz
    exact hr.ne' hzero.symm
  have hrightPoint :
      ∀ z ∈ Metric.sphere (1 : ℂ) r,
        resolvent (S beta) z * P = (z - 1)⁻¹ • P := by
    intro z hz
    have hzRes : z ∈ resolventSet ℂ (S beta) :=
      hres hz
    have hzNe : z - 1 ≠ 0 :=
      sub_ne_zero.mpr (hSphereNe z hz)
    have hResidue :=
      resolvent_mul_fixedSector_residue (S beta) P z hSP hzRes
    have hScaled :=
      congrArg (fun X : A => (z - 1)⁻¹ • X) hResidue
    simpa [smul_smul, hzNe] using hScaled
  have hleftPoint :
      ∀ z ∈ Metric.sphere (1 : ℂ) r,
        P * resolvent (S beta) z = (z - 1)⁻¹ • P := by
    intro z hz
    have hzRes : z ∈ resolventSet ℂ (S beta) :=
      hres hz
    have hzNe : z - 1 ≠ 0 :=
      sub_ne_zero.mpr (hSphereNe z hz)
    have hResidue :=
      fixedSector_mul_resolvent_residue (S beta) P z hPS hzRes
    have hScaled :=
      congrArg (fun X : A => (z - 1)⁻¹ • X) hResidue
    simpa [smul_smul, hzNe] using hScaled
  have hpoleIntegral :
      (∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P) =
        (2 * Real.pi * Complex.I : ℂ) • P := by
    rw [circleIntegral.integral_smul_const]
    have hmem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) r := by
      rw [Metric.mem_ball]
      simpa using hr
    rw [circleIntegral.integral_sub_inv_of_mem_ball hmem]
  have hrightIntegral :
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z * P) =
        (2 * Real.pi * Complex.I : ℂ) • P := by
    calc
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z * P) =
          ∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P := by
            apply circleIntegral.integral_congr hr.le
            intro z hz
            exact hrightPoint z hz
      _ = (2 * Real.pi * Complex.I : ℂ) • P := hpoleIntegral
  have hleftIntegral :
      (∮ z in C((1 : ℂ), r), P * resolvent (S beta) z) =
        (2 * Real.pi * Complex.I : ℂ) • P := by
    calc
      (∮ z in C((1 : ℂ), r), P * resolvent (S beta) z) =
          ∮ z in C((1 : ℂ), r), (z - 1)⁻¹ • P := by
            apply circleIntegral.integral_congr hr.le
            intro z hz
            exact hleftPoint z hz
      _ = (2 * Real.pi * Complex.I : ℂ) • P := hpoleIntegral
  let rightMul : A →L[ℂ] A :=
    ((ContinuousLinearMap.mulLeftRight ℂ A) (1 : A)) P
  let leftMul : A →L[ℂ] A :=
    ((ContinuousLinearMap.mulLeftRight ℂ A) P) (1 : A)
  have hrightMap :
      rightMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
        ∮ z in C((1 : ℂ), r), rightMul (resolvent (S beta) z) := by
    unfold circleIntegral
    calc
      rightMul
          (∫ theta in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap (1 : ℂ) r) theta •
              resolvent (S beta) (circleMap (1 : ℂ) r theta)) =
        ∫ theta in (0 : ℝ)..2 * Real.pi,
          rightMul
            (deriv (circleMap (1 : ℂ) r) theta •
              resolvent (S beta) (circleMap (1 : ℂ) r theta)) := by
              exact
                (ContinuousLinearMap.intervalIntegral_comp_comm
                  (𝕜 := ℂ) rightMul hresIntegrable.out).symm
      _ =
        ∫ theta in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap (1 : ℂ) r) theta •
            rightMul (resolvent (S beta) (circleMap (1 : ℂ) r theta)) := by
              apply intervalIntegral.integral_congr
              intro theta htheta
              exact rightMul.map_smul _ _
  have hleftMap :
      leftMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
        ∮ z in C((1 : ℂ), r), leftMul (resolvent (S beta) z) := by
    unfold circleIntegral
    calc
      leftMul
          (∫ theta in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap (1 : ℂ) r) theta •
              resolvent (S beta) (circleMap (1 : ℂ) r theta)) =
        ∫ theta in (0 : ℝ)..2 * Real.pi,
          leftMul
            (deriv (circleMap (1 : ℂ) r) theta •
              resolvent (S beta) (circleMap (1 : ℂ) r theta)) := by
              exact
                (ContinuousLinearMap.intervalIntegral_comp_comm
                  (𝕜 := ℂ) leftMul hresIntegrable.out).symm
      _ =
        ∫ theta in (0 : ℝ)..2 * Real.pi,
          deriv (circleMap (1 : ℂ) r) theta •
            leftMul (resolvent (S beta) (circleMap (1 : ℂ) r theta)) := by
              apply intervalIntegral.integral_congr
              intro theta htheta
              exact leftMul.map_smul _ _
  have hrightPush :
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z) * P =
        ∮ z in C((1 : ℂ), r), resolvent (S beta) z * P := by
    calc
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z) * P =
          rightMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) := by
            simp [rightMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = ∮ z in C((1 : ℂ), r), rightMul (resolvent (S beta) z) := hrightMap
      _ = ∮ z in C((1 : ℂ), r), resolvent (S beta) z * P := by
            apply circleIntegral.integral_congr hr.le
            intro z hz
            simp [rightMul, ContinuousLinearMap.mulLeftRight_apply]
  have hleftPush :
      P * (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
        ∮ z in C((1 : ℂ), r), P * resolvent (S beta) z := by
    calc
      P * (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
          leftMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) := by
            simp [leftMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = ∮ z in C((1 : ℂ), r), leftMul (resolvent (S beta) z) := hleftMap
      _ = ∮ z in C((1 : ℂ), r), P * resolvent (S beta) z := by
            apply circleIntegral.integral_congr hr.le
            intro z hz
            simp [leftMul, ContinuousLinearMap.mulLeftRight_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  change
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) * P = P ∧
      P * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) = P
  have hrightRaw :
      (∮ z in C((1 : ℂ), r), resolvent (S beta) z) * P =
        (2 * Real.pi * Complex.I : ℂ) • P :=
    hrightPush.trans hrightIntegral
  have hleftRaw :
      P * (∮ z in C((1 : ℂ), r), resolvent (S beta) z) =
        (2 * Real.pi * Complex.I : ℂ) • P :=
    hleftPush.trans hleftIntegral
  constructor
  · calc
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) * P =
        rightMul
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) := by
              simp [rightMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          rightMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) := by
            exact rightMul.map_smul _ _
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((∮ z in C((1 : ℂ), r), resolvent (S beta) z) * P) := by
            simp [rightMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((2 * Real.pi * Complex.I : ℂ) • P) := by
            rw [hrightRaw]
      _ = P := by
            rw [smul_smul, inv_mul_cancel₀ htwoPiI, one_smul]
  · calc
      P * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) =
        leftMul
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) := by
              simp [leftMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          leftMul (∮ z in C((1 : ℂ), r), resolvent (S beta) z) := by
            exact leftMul.map_smul _ _
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (P * (∮ z in C((1 : ℂ), r), resolvent (S beta) z)) := by
            simp [leftMul, ContinuousLinearMap.mulLeftRight_apply]
      _ = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ((2 * Real.pi * Complex.I : ℂ) • P) := by
            rw [hleftRaw]
      _ = P := by
            rw [smul_smul, inv_mul_cancel₀ htwoPiI, one_smul]

end

end MathlibAnalytic
end MGAP4D
