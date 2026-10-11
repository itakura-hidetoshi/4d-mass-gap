import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorReferenceL2FormBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialResidualKernel
import Mathlib.Tactic

/-!
# P4-Q2-BF: original Wilson reference bounded by intrinsic centered variance

BE bounds the actual physical Wilson mass-weighted right/left all-link Haar
reference above by twelve times the genuine joint L² norm squared. Here the
canonical joint constant-line projection B is used to remove the constant
component with NO small-beta premise and NO volume-dependent loss.

The existing qualitative twelve-color residual-kernel theorem says every
vector in the intrinsic constant line is fixed by all twelve physical
conditional expectations. Their linearity therefore identifies the residual
energy of f exactly with the residual energy of f - B f.

This gives the sharpened, cutoff-free upper comparison

  originalReferenceReal(F) ≤ 12 E12(f) ≤ 12 ‖f - B f‖².

The original reference thus vanishes for bounded concrete observables whose
physical joint L² representatives belong to the constant line. On the
certified G1 interval, this upper bound can be packaged with the independent
positive relative Poincare lower bound κ ‖f - B f‖² ≤ E12(f).

The inequalities are NOT reversed. In particular no lower Poincare estimate
for the original Haar reference, continuity on the full L² quotient, or
continuum spacing-scaled Yang-Mills mass gap is claimed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1500000

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

section

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

/-- Every genuine physical twelve-spatial conditional expectation fixes the
intrinsic orthogonal constant projection of an arbitrary joint L² vector.
This uses the established exact kernel, not independence of color operators. -/
theorem p4Q2BF_twelveSpatialCondExp_fixes_jointConstantProjection
    (f : J) (c : C12) :
    P12 c (B f) = B f := by
  have hmem : B f ∈ C := by
    change C.starProjection f ∈ C
    exact C.starProjection_apply_mem f
  have hzero : E12 (B f) = 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta (B f)).2 hmem
  exact
    (groundStateJointColorNormalizedResidualEnergy_eq_zero_iff_fixed
      P12 (B f)).1 hzero c

/-- Removing the intrinsic physical joint constant-line projection does not
change the canonical twelve-color residual energy, for every beta ≥ 0.
This is an EXACT equality on the original physical joint Hilbert carrier. -/
theorem p4Q2BF_physicalTwelveResidualEnergy_centered_eq
    (f : J) :
    E12 (f - B f) = E12 f := by
  have hfixed :
      ∀ c : C12, P12 c (B f) = B f :=
    fun c => p4Q2BF_twelveSpatialCondExp_fixes_jointConstantProjection
      H N hN beta hbeta f c
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    groundStateJointColorNormalizedResidualEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  have hres :
      (f - B f) - P12 c (f - B f) = f - P12 c f := by
    rw [map_sub, hfixed c]
    abel
  rw [hres]

/-- Stronger than the all-beta BE bound E12(f) ≤ ‖f‖²: the actual
twelve-color residual is bounded by only the squared norm transverse to
the intrinsic constant line. No high-temperature assumption is necessary. -/
theorem p4Q2BF_physicalTwelveResidualEnergy_le_centeredJointNormSq
    (f : J) :
    E12 f ≤ ‖f - B f‖ ^ 2 := by
  rw [← p4Q2BF_physicalTwelveResidualEnergy_centered_eq
    H N hN beta hbeta f]
  exact
    p4Q2BE_physicalTwelveResidualEnergy_le_jointNormSq
      H N hN beta hbeta (f - B f)

/-- Sharpen the TRUE original Wilson mass-weighted all-link right/left Haar
reference upper bound to the physical joint constant-centered variance.
The coefficient 12 comes only from the twelve normalized colors; neither
the lattice-link count nor a beta cutoff enters. -/
theorem p4Q2BF_originalWilsonReferenceReal_le_twelve_centeredVariance
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤
      (12 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          B (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2 := by
  let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
  calc
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F ≤
        (12 : ℝ) * E12 f :=
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
        H N hN beta hbeta F hF bound hbound
    _ ≤ (12 : ℝ) * ‖f - B f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (p4Q2BF_physicalTwelveResidualEnergy_le_centeredJointNormSq
          H N hN beta hbeta f) (by norm_num)

/-- The genuine bounded-core reference vanishes on ALL original physical
joint L² constant-line representatives (not only the zero representative). -/
theorem p4Q2BF_originalWilsonReferenceReal_eq_zero_of_jointConstantProjection
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hconst :
      p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound =
        B (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)) :
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F = 0 := by
  have hnonneg :
      0 ≤ p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F := by
    unfold p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
    exact ENNReal.toReal_nonneg
  have hupper :=
    p4Q2BF_originalWilsonReferenceReal_le_twelve_centeredVariance
      H N hN beta hbeta F hF bound hbound
  rw [hconst, sub_self, norm_zero] at hupper
  have hle :
      p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
        H N hN beta hbeta F ≤ 0 := by
    nlinarith
  exact le_antisymm hle hnonneg

/-- BF main: the genuine normalized twelve-spatial residual is sandwiched
between a strictly positive high-temperature coefficient and the exact
constant-centered joint L² variance, while the original Wilson reference
is controlled only in the proved upper-comparison direction. -/
theorem p4Q2BF_originalWilsonReference_and_twelveSpatial_centeredSandwich
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    let f := p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta * ‖f - B f‖ ^ 2 ≤ E12 f ∧
    E12 f ≤ ‖f - B f‖ ^ 2 ∧
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤ (12 : ℝ) * E12 f ∧
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F ≤ (12 : ℝ) * ‖f - B f‖ ^ 2 := by
  dsimp
  refine ⟨
    p4Q2BD_boundedOriginalWilsonJointSchurRelativePoincare
      H N hN beta hbeta s hs hcut F hF bound hbound,
    p4Q2BF_physicalTwelveResidualEnergy_le_centeredJointNormSq
      H N hN beta hbeta
      (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound),
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
      H N hN beta hbeta F hF bound hbound,
    p4Q2BF_originalWilsonReferenceReal_le_twelve_centeredVariance
      H N hN beta hbeta F hF bound hbound⟩

end
end

end MathlibAnalytic
end MGAP4D
