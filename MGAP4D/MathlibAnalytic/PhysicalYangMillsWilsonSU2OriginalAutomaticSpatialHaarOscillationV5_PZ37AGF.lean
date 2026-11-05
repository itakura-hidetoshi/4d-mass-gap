import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalContinuousSpatialHaarCellwiseV5_PZ37AGE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGF — unconditional genuine spatial Haar oscillation envelope

AGE correctly separated genuine ZW physical L2 source and its equal-a.e.
continuous Wilson representative, but retained an explicit independent
physical cellwise-oscillation certificate as an input.

AGF eliminates THAT input without new physical hypotheses: AFZ's true
centered spatial Wilson action is bounded at EVERY configuration by
the original spatial plaquette count p_H. The genuine centered one-slab
kernel has true midpoint radius (1-k_H)/2, proved in AGB.

Thus the genuine continuous signed integrand g_B satisfies

  |g_B(A)| <= (1-k_H)*p_H/2
  |g_B(A)-g_B(C)| <= (1-k_H)*p_H <= p_H

for ANY original spatial configurations A,C, uniformly in the true
right boundary B. These are conservative global bounds and therefore
also apply to every actual AGD 24^L spatial cell.

This yields a constructed AGE physical oscillation certificate with no
external oracle, and closes the genuine AGD/AGE rational signed transfer
quadrature error with explicit epsilon=p_H (a rational plaquette count).
The finite rational center table itself uses AGE's noncomputable
rational-density choices, not measured or computably certified values.

The coarse envelope does not prove actual nonzero transfer signs, a
two-sign shell, volume-uniform coercivity, Hamiltonian spectral gap or
the continuum 4D Yang-Mills mass gap. A future stage must tighten the
error using actual one-link geometry and concrete center evaluation.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "CellIndex" =>
  Fin (Fintype.card (p4Q2PZ37AGD_spatialGridIndex H))
local notation "cells" => p4Q2PZ37AGD_toAGCOriginalHaarCells H

local instance p4Q2PZ37AGF_links : Fintype Link := Fintype.ofFinite _

/-- The actual centered continuous source is pointwise bounded by the
literal original spatial-plaquette count. This statement is about the
continuous representative, not arbitrary pointwise evaluation of L2. -/
theorem p4Q2PZ37AGF_originalContinuousSource_abs_le
    (A : Cfg) :
    |fCont A| ≤ pH := by
  obtain ⟨hm0, hm1⟩ := p4Q2PZ37AFZ_originalWilsonMean_bounds H
  have hW0 : 0 ≤ Wc A :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) A
  have hW1 : Wc A ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) A
  change |(1 / 2 : ℝ) * (Wc A - mH * 1)| ≤ pH
  apply abs_le.mpr
  constructor <;> linarith only [hm0, hm1, hW0, hW1]

/-- The actual original action count is nonnegative. -/
theorem p4Q2PZ37AGF_plaquetteCount_nonneg : 0 ≤ pH := by
  unfold p4Q2PZ37AFZ_plaquetteCount
  positivity

/-- The centered genuine Wilson one-slab kernel is globally bounded
by its original action floor; no proxy posterior is inserted. -/
theorem p4Q2PZ37AGF_originalContinuousIntegrand_abs_le_floor
    (B A : Cfg) :
    |gCont B A| ≤ ((1 - kFloor) / 2) * pH := by
  have hf : |fCont A| ≤ pH :=
    p4Q2PZ37AGF_originalContinuousSource_abs_le H A
  have hk : |K A B - (1 + kFloor) / 2| ≤ (1 - kFloor) / 2 :=
    p4Q2PZ37AGB_originalKernel_centeredMidpointBound H A B
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  change |fCont A * (K A B - (1 + kFloor) / 2)| ≤
    ((1 - kFloor) / 2) * pH
  rw [abs_mul]
  calc
    |fCont A| * |K A B - (1 + kFloor) / 2| ≤
      pH * ((1 - kFloor) / 2) :=
        mul_le_mul hf hk (abs_nonneg _) hp
    _ = ((1 - kFloor) / 2) * pH := by ring

/-- Universal true-Wilson oscillation modulus, valid for ANY pair of
spatial configurations and therefore each actual AGD product cell. -/
theorem p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation
    (B A C : Cfg) :
    |gCont B A - gCont B C| ≤ pH * (1 - kFloor) := by
  have hA := p4Q2PZ37AGF_originalContinuousIntegrand_abs_le_floor H B A
  have hC := p4Q2PZ37AGF_originalContinuousIntegrand_abs_le_floor H B C
  calc
    |gCont B A - gCont B C| ≤
      |gCont B A| + |gCont B C| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (gCont B A) (0 : ℝ) (gCont B C))
    _ ≤ ((1 - kFloor) / 2) * pH +
      ((1 - kFloor) / 2) * pH := add_le_add hA hC
    _ = pH * (1 - kFloor) := by ring

/-- No external oscillation input: the genuine kernel floor and spatial
Wilson action produce a sharp-for-this-global-range certificate. -/
def p4Q2PZ37AGF_unconditionalFloorOscillation
    (B : Cfg) :
    p4Q2PZ37AGE_originalSpatialOscillation H B where
  epsilon := pH * (1 - kFloor)
  epsilon_nonneg := by
    have hp := p4Q2PZ37AGF_plaquetteCount_nonneg H
    have he := p4Q2PZ37AGB_originalKernel_radius_nonneg H
    apply mul_nonneg hp
    linarith only [he]
  hOsc := by
    intro i A hA
    exact p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation H B A
      (p4Q2PZ37AGE_spatialProductCenter H i)

/-- Fully rational conservative fallback epsilon=p_H. The positive
kernel floor implies 1-k_H≤1 without numerical evaluation of k_H. -/
theorem p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation_le_count
    (B A C : Cfg) :
    |gCont B A - gCont B C| ≤ pH := by
  have h := p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation H B A C
  have hp := p4Q2PZ37AGF_plaquetteCount_nonneg H
  have hk : 0 ≤ kFloor :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H b0).le
  calc
    |gCont B A - gCont B C| ≤ pH * (1 - kFloor) := h
    _ ≤ pH * 1 := mul_le_mul_of_nonneg_left (by linarith only [hk]) hp
    _ = pH := by ring

/-- Concrete original AGD cellwise oscillation certificate with no
external modulus, source, probability, finite grid, or receiver input. -/
def p4Q2PZ37AGF_unconditionalRationalOscillation
    (B : Cfg) :
    p4Q2PZ37AGE_originalSpatialOscillation H B where
  epsilon := pH
  epsilon_nonneg := p4Q2PZ37AGF_plaquetteCount_nonneg H
  hOsc := by
    intro i A hA
    exact p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation_le_count H
      B A (p4Q2PZ37AGE_spatialProductCenter H i)

/-- The true signed transfer now has a proof-carrying AGD/AGE
rational-center error with NO external physical oscillation oracle. -/
theorem p4Q2PZ37AGF_originalSignedTransfer_noOscillationInput
    (B : Cfg) :
    |decomposableOneSliceTransferIntegral H 2 b0
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B -
      (p4Q2PZ37AGC_HaarCenter (p4Q2PZ37AGD_toAGCOriginalHaarCells H)
        (p4Q2PZ37AGE_originalSpatialSample H B) : ℝ)| ≤
      p4Q2PZ37AGC_HaarTotalError (p4Q2PZ37AGD_toAGCOriginalHaarCells H)
        (p4Q2PZ37AGE_originalSpatialSample H B)
        (pH + (1 / 64 : ℝ)) :=
  p4Q2PZ37AGE_originalSignedTransfer_accuracy H B
    (p4Q2PZ37AGF_unconditionalRationalOscillation H B)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_originalContinuousSource_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_plaquetteCount_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_originalContinuousIntegrand_abs_le_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_unconditionalFloorOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_originalContinuousIntegrand_globalOscillation_le_count
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_unconditionalRationalOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGF_originalSignedTransfer_noOscillationInput
