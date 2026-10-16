import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalZeroModeLinkTransferContinuityV5_HX
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoWilsonPosteriorSourceExpectationGapV5_GI
import Mathlib.Tactic

/-!
# P4-Q2-HY: actual fine-right zero-depth source is detected by original Wilson GI

The independent Haar conditional is NEVER used in this proof.
The true ORIGINAL Wilson physical one-slab transfer is strictly
positive for the actual fine-right zero-depth source (GV), and its
right-link SU(2) dependence is continuous (HX). The ORIGINAL two
interacting Wilson conditional posterior densities are positive,
continuous, normalized and genuinely distinct at frozen beta>0
(GQ/FX, with literal SU(2) two-row density witnesses FS).
GR expresses the original signed physical receiver as a transfer
value minus a posterior-half-density-weighted transfer value.
GI expresses its actual two-posterior expectation difference as
Haar pairing with the literal density-row contrast.

The verified abstract HV/HW two-density Hellinger noncancellation
then proves: for EVERY actual spatial link e and right configuration,
the same physical fine-right zero-depth source has NONZERO original GI
expectation gap at at least one of the TWO genuine original Wilson
left boundary contexts (identity or pi rotation). The left boundary
choice may depend on the physical context. This is a true physical
source witness, NOT just positivity of a different squared receiver.

This is qualitative and finite-volume; it does not provide uniform
gap/frame constants or all-depth physical source separation, H1-C3,
Hamiltonian or continuum 4D Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3400000
set_option synthInstance.maxHeartbeats 950000

local instance p4Q2HY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2HY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2HY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2HY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2HY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2HY_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

section PhysicalOriginal

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- A positive and right-link-continuous ACTUAL physical source transfer
is detected by the difference of the two interacting Wilson
posteriors at either original physical left boundary.
All posterior normalization, distinctness, and full-support assumptions
are discharged by existing concrete finite SU(2) Wilson theorems. -/
theorem p4Q2HY_originalWilsonGI_two_left_boundary_detects_positive_source
    (hFrozen : 0 < beta) (f : Phys) (right : Cfg) (e : Link)
    (hTcont : Continuous (fun g : Gauge =>
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g)))
    (hTpos : ∀ g : Gauge, 0 <
      decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g)) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e (originalWilsonExplicitIdentityBoundary H, right) ≠ 0 ∨
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H beta hbeta f e (p4Q2FQ_originalSU2LeftPiRotationAtLink H e, right) ≠ 0 := by
  let μ : Measure Gauge := normalizedCompactHaar Gauge
  let left0 : Cfg := originalWilsonExplicitIdentityBoundary H
  let left1 : Cfg := p4Q2FQ_originalSU2LeftPiRotationAtLink H e
  let L : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖⁻¹
  let T : Gauge → ℝ := fun g =>
    decomposableOneSliceTransferIntegral H 2 beta f
      (Function.update right e g)
  let P0 : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta left0 right e g
  let P1 : Gauge → ℝ := fun g =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta left1 right e g
  have hP0 : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta hbeta left0 right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta left0 right e)
  have hP1 : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta hbeta left1 right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta left1 right e)
  have hP0pos (g : Gauge) : 0 < P0 g :=
    p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left0 right e g
  have hP1pos (g : Gauge) : 0 < P1 g :=
    p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left1 right e g
  have hP0mass : (∫ g, P0 g ∂μ) = 1 := by
    change (∫ g, continuousNormalizedExp μ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta left0 right e) g ∂μ) = 1
    exact integral_continuousNormalizedExp_eq_one μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta left0 right e)
  have hP1mass : (∫ g, P1 g ∂μ) = 1 := by
    change (∫ g, continuousNormalizedExp μ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
        H 2 (by norm_num) beta hbeta left1 right e) g ∂μ) = 1
    exact integral_continuousNormalizedExp_eq_one μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta left1 right e)
  have hMass : (∫ g, P0 g ∂μ) = (∫ g, P1 g ∂μ) :=
    hP0mass.trans hP1mass.symm
  have hDifferent : ∃ g : Gauge, P0 g ≠ P1 g := by
    have hFS :=
      p4Q2FS_originalSU2EveryLinkTruePosteriorDensity_leftSensitive
        H beta hFrozen right e
    rcases hFS with hOne | hPi
    · exact ⟨1, hOne⟩
    · exact ⟨specialUnitaryTwoRotation Real.pi, hPi⟩
  have hFull (U : Set Gauge) (hU : IsOpen U) (hUnonempty : U.Nonempty) :
      0 < μ U := hU.measure_pos μ hUnonempty
  have hL : 0 < L := by
    dsimp [L]
    exact inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta hbeta)
  have hUpdate : Function.update right e (right e) = right :=
    Function.update_eq_self e right
  have hGR0 (g : Gauge) :
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e ((left0, right), g) =
      L * (T (right e) -
        Real.sqrt (P0 (right e)) / Real.sqrt (P0 g) * T g) := by
    have hh := p4Q2GR_originalSignedResponse_at_inserted_right
      H beta hbeta f left0 right e g (right e)
    simpa only [hUpdate, L, T, P0, left0] using hh
  have hGR1 (g : Gauge) :
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e ((left1, right), g) =
      L * (T (right e) -
        Real.sqrt (P1 (right e)) / Real.sqrt (P1 g) * T g) := by
    have hh := p4Q2GR_originalSignedResponse_at_inserted_right
      H beta hbeta f left1 right e g (right e)
    simpa only [hUpdate, L, T, P1, left1] using hh
  have hGI0 :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta f e (left0, right) =
      ∫ g : Gauge,
        (L * (T (right e) -
          Real.sqrt (P0 (right e)) / Real.sqrt (P0 g) * T g)) *
          (P0 g - P1 g) ∂μ := by
    calc
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta hbeta f e (left0, right) =
        ∫ g : Gauge,
          p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
            H 2 (by norm_num) beta hbeta f e ((left0, right), g) *
            p4Q2GB_originalWilsonPosteriorLeftDensityContrast
              H beta hbeta right e g ∂μ :=
          p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing
            H beta hbeta f e (left0, right)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with g
        rw [hGR0 g]
        rfl
  have hGI1 :
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H beta hbeta f e (left1, right) =
      ∫ g : Gauge,
        (L * (T (right e) -
          Real.sqrt (P1 (right e)) / Real.sqrt (P1 g) * T g)) *
          (P0 g - P1 g) ∂μ := by
    calc
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H beta hbeta f e (left1, right) =
        ∫ g : Gauge,
          p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
            H 2 (by norm_num) beta hbeta f e ((left1, right), g) *
            p4Q2GB_originalWilsonPosteriorLeftDensityContrast
              H beta hbeta right e g ∂μ :=
          p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing
            H beta hbeta f e (left1, right)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with g
        rw [hGR1 g]
        rfl
  have hHW :=
    p4Q2HW_two_normalized_relative_receiver_gaps_not_both_zero
      μ hFull T P0 P1 L hTcont hP0 hP1 hTpos
      hP0pos hP1pos hDifferent hMass hL (right e)
  rcases hHW with h0 | h1
  · left
    rw [show originalWilsonExplicitIdentityBoundary H = left0 from rfl]
    rw [hGI0]
    exact h0
  · right
    rw [show p4Q2FQ_originalSU2LeftPiRotationAtLink H e = left1 from rfl]
    rw [hGI1]
    exact h1

end PhysicalOriginal

section ActualZeroDepth

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- The genuine fine-right zero-depth Krylov physical unit is GI-detected
at EVERY original finite SU(2) right background and spatial link:
one of the two actual Wilson left-boundary contexts necessarily has
nonzero original two-posterior expectation gap. No source frame or
independent Haar posterior is postulated. -/
theorem p4Q2HY_actualRightZeroDepth_originalWilsonGI_anchor_nonzero
    (hFrozen : 0 < beta n) (right : Cfg) (e : Link) :
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (RightFactor n 0) e
        (originalWilsonExplicitIdentityBoundary Hn, right) ≠ 0 ∨
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      Hn (beta n) (hbeta n) (RightFactor n 0) e
        (p4Q2FQ_originalSU2LeftPiRotationAtLink Hn e, right) ≠ 0 := by
  apply p4Q2HY_originalWilsonGI_two_left_boundary_detects_positive_source
    Hn (beta n) (hbeta n) hFrozen (RightFactor n 0) right e
  · exact p4Q2HX_actualFineRightZeroDepth_originalWilsonTransfer_link_continuous
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n right e
  · intro g
    exact p4Q2GV_actualFineRightZeroMode_transferIntegral_pos
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (Function.update right e g)

end ActualZeroDepth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HY_originalWilsonGI_two_left_boundary_detects_positive_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2HY_actualRightZeroDepth_originalWilsonGI_anchor_nonzero
