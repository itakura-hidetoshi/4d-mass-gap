import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalBoundarySwapProjectionIntertwining
import Mathlib.Tactic

/-!
# P4-Q2-DN: original Wilson left-link fiber = original UNSWAPPED CR defect

DM proved on ALL genuine original independent pair-Haar Hilbert-L²
that the authentic physical endpoint-swap isometry intertwines
left and right coordinate conditional-expectation projections.

DL had identified each physical original Wilson LEFT-link Haar fiber
variance with the CR RIGHT-link squared defect of the endpoint-SWAPPED
representative. This module uses the exact DM intertwining and L²
isometry, not an equality of unequal Wilson and Haar means, to identify
that original LEFT reference quantity with the corresponding
UNSWAPPED original physical left-coordinate CR defect for every
bounded strongly measurable concrete observable.

Together with DK's already proved original RIGHT-link Hilbert identity,
we now have BOTH actual physical endpoints on the SAME original,
independent pair-Haar Hilbert space. The remaining original Wilson
twelve-color lower-coercivity/finite-volume Poincare arithmetic and
the volume-uniform or continuum mass gap are separate steps.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "muH" => normalizedCompactHaar G
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "U" => p4Q2DM_originalPairHaarSwapL2 H N
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- DM's full-L² projection intertwining and literal norm-preserving
physical endpoint swap identify swapped-right and unswapped-left
squared Hilbert defects for EVERY genuine pair-Haar L² class. -/
theorem p4Q2DN_originalLeftDefect_eq_swapRightDefect
    (target : Link) (f : JH) :
    ‖U f - P (Sum.inr target) (U f)‖ ^ 2 =
      ‖f - P (Sum.inl target) f‖ ^ 2 := by
  rw [p4Q2DM_actualPairHaarProjection_swap_intertwining H N target f]
  rw [← map_sub]
  exact congrArg (fun x : ℝ => x ^ 2) ((p4Q2DM_originalPairHaarSwapL2 H N).norm_map _)

/-- A concrete bounded original physical joint observable and its
canonical DL-swapped pair-Haar L² class are exactly related by applying
the genuine DM physical Hilbert endpoint-swap isometry to its
UNSWAPPED pair-Haar L² class. -/
theorem p4Q2DN_canonicalSwappedPairHaarL2_eq_swapUnitary
    (f : JH) (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    p4Q2DL_swappedPairHaarL2 H N F hF M hM = U f := by
  apply Lp.ext
  have hSwappedRepresentative :=
    p4Q2DL_swappedPairHaarL2_ae_eq H N F hF M hM
  have hSwappedInput :
      p4Q2BB_swapConcrete H N F =ᵐ[muPair]
        (fun z : Joint => (f : Joint → ℝ) z.swap) := by
    simpa only [p4Q2BB_swapConcrete, Function.comp_def] using
      (p4Q2DM_originalPairHaar_swap_measurePreserving H N).quasiMeasurePreserving.ae_eq
        hEq
  have hSwappedOutput :=
    p4Q2DM_originalPairHaarSwapL2_ae H N f
  exact hSwappedRepresentative.symm.trans
    (hSwappedInput.trans hSwappedOutput.symm)

/-- The actual original Wilson LEFT Haar fiber variance, on the
literal left-boundary-Haar × retained-right-Haar outer probability,
equals the UNSWAPPED left-coordinate CR Hilbert-L² defect squared
for the SAME concrete bounded real joint observable. No surrogate
measure, new assumptions or Wilson posterior commutation is used. -/
theorem p4Q2DN_originalLeftHaarFiberVariance_eq_CR_left_defect
    (target : Link) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    (∫⁻ ctx : Cfg ×
       (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
      evariance
        (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
        muH
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            muH)))) =
      ENNReal.ofReal (‖f - P (Sum.inl target) f‖ ^ 2) := by
  let fs : JH := p4Q2DL_swappedPairHaarL2 H N F hF M hM
  have hFs : fs = U f :=
    p4Q2DN_canonicalSwappedPairHaarL2_eq_swapUnitary
      H N f F hF M hM hEq
  have hDL :
      (∫⁻ ctx : Cfg ×
         (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
        evariance
          (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
          muH
        ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              muH)))) =
        ENNReal.ofReal (‖fs - P (Sum.inr target) fs‖ ^ 2) := by
    simpa only [fs] using
      (p4Q2DL_originalLeftHaarFiberVariance_eq_canonicalSwappedDefect
        H N target F hF M hM)
  calc
    (∫⁻ ctx : Cfg ×
       (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → G),
      evariance
        (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
        muH
      ∂((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            muH)))) =
        ENNReal.ofReal (‖fs - P (Sum.inr target) fs‖ ^ 2) := hDL
    _ = ENNReal.ofReal (‖U f - P (Sum.inr target) (U f)‖ ^ 2) := by
      rw [hFs]
    _ = ENNReal.ofReal (‖f - P (Sum.inl target) f‖ ^ 2) :=
      congrArg ENNReal.ofReal
        (p4Q2DN_originalLeftDefect_eq_swapRightDefect H N target f)

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
