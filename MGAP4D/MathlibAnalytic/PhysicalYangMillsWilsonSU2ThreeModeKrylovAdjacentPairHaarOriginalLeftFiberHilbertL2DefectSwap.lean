import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRightFiberHilbertL2Defect
import Mathlib.Tactic

/-!
# P4-Q2-DL: original left Haar fiber variance as a genuine Hilbert L² defect

DK proved the exact ORIGINAL right Wilson split Haar fiber variance equals
the actual pair-Haar CR Hilbert-L² right-coordinate defect. BB's physical
left-link reference uses the original boundary swap, not a surrogate law.

This module constructs a GENUINE pair-Haar L² representative of that
swapped bounded physical observable and applies DK to show that every
left-link unweighted Haar fiber variance is exactly an authentic CR
right-coordinate defect of the swapped L² observable.

This completes the LEFT half of the reference-variance Hilbert
identification at the swapped-presentation level, preserving the original
physical configuration, Haar law and endpoint-swap action. Identifying
the swapped right-coordinate defect with the original left-coordinate
defect is a separate intertwining obligation before coercivity.
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

/-- DK's context abbreviation is private to its Lean module. Reconstruct
the SAME physical left-Haar × off-right-Haar product transparently here. -/
private abbrev p4Q2DL_rightContext (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

private noncomputable def p4Q2DL_rightOuterHaar (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (p4Q2DL_rightContext H N target) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))

section ActualLeftLink
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
local notation "Section" =>
  periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection H N

/-- The original BB left-boundary Haar fiber is precisely a right-boundary
Haar fiber of the original *swapped* concrete physical observable.
The exact same outer Haar product and normalized SU(N) Haar are retained. -/
theorem p4Q2DL_originalLeftHaarFiberVariance_eq_swappedCR_defect
    (target : Link) (fSwap : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hSwap : p4Q2BB_swapConcrete H N F =ᵐ[muPair]
      (fSwap : Joint → ℝ)) :
    (∫⁻ ctx : p4Q2DL_rightContext H N target,
      evariance
        (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
        muH
      ∂(p4Q2DL_rightOuterHaar H N target)) =
        ENNReal.ofReal
          (‖fSwap - P (Sum.inr target) fSwap‖ ^ 2) := by
  exact p4Q2DK_originalRightHaarFiberVariance_eq_CR_defect
    H N target fSwap (p4Q2BB_swapConcrete H N F)
    (p4Q2BB_swapConcrete_stronglyMeasurable H N F hF)
    M (p4Q2BB_swapConcrete_norm_le H N F M hM) hSwap

/-- A bounded original physical left/right observable has a CANONICAL
real pair-Haar Hilbert-L² class after swapping actual endpoints.
No arbitrary representative is assumed and no new measure is used. -/
noncomputable def p4Q2DL_swappedPairHaarL2
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) : JH := by
  letI : IsProbabilityMeasure muPair := by infer_instance
  let FS : Joint → ℝ := p4Q2BB_swapConcrete H N F
  have hSm : StronglyMeasurable FS :=
    p4Q2BB_swapConcrete_stronglyMeasurable H N F hF
  have hBd : ∀ z, ‖FS z‖ ≤ M :=
    p4Q2BB_swapConcrete_norm_le H N F M hM
  have hLp : MemLp FS 2 muPair :=
    MemLp.of_bound hSm.aestronglyMeasurable M
      (Filter.Eventually.of_forall hBd)
  exact hLp.toLp FS

/-- The canonical swapped pair-Haar Hilbert class truly represents
BB's physical endpoint-swap observable on the original pair-Haar law. -/
theorem p4Q2DL_swappedPairHaarL2_ae_eq
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) :
    p4Q2BB_swapConcrete H N F =ᵐ[muPair]
      (p4Q2DL_swappedPairHaarL2 H N F hF M hM : Joint → ℝ) := by
  letI : IsProbabilityMeasure muPair := by infer_instance
  let FS : Joint → ℝ := p4Q2BB_swapConcrete H N F
  have hSm : StronglyMeasurable FS :=
    p4Q2BB_swapConcrete_stronglyMeasurable H N F hF
  have hBd : ∀ z, ‖FS z‖ ≤ M :=
    p4Q2BB_swapConcrete_norm_le H N F M hM
  have hLp : MemLp FS 2 muPair :=
    MemLp.of_bound hSm.aestronglyMeasurable M
      (Filter.Eventually.of_forall hBd)
  exact (MemLp.coeFn_toLp hLp).symm

/-- For EVERY bounded strongly measurable physical observable, the
original LEFT Wilson Haar fiber variance equals the authentic Hilbert
coordinate defect of its ACTUAL endpoint-swapped pair-Haar L² class. -/
theorem p4Q2DL_originalLeftHaarFiberVariance_eq_canonicalSwappedDefect
    (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M) :
    (∫⁻ ctx : p4Q2DL_rightContext H N target,
      evariance
        (Section target (p4Q2BB_swapConcrete H N F) ctx.1 ctx.2)
        muH
      ∂(p4Q2DL_rightOuterHaar H N target)) =
        ENNReal.ofReal
          (‖p4Q2DL_swappedPairHaarL2 H N F hF M hM -
             P (Sum.inr target)
               (p4Q2DL_swappedPairHaarL2 H N F hF M hM)‖ ^ 2) := by
  exact p4Q2DL_originalLeftHaarFiberVariance_eq_swappedCR_defect
    H N target
    (p4Q2DL_swappedPairHaarL2 H N F hF M hM)
    F hF M hM
    (p4Q2DL_swappedPairHaarL2_ae_eq H N F hF M hM)

end ActualLeftLink
end

end MathlibAnalytic
end MGAP4D
