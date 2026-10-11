import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointL2ContinuousBilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic

/-!
# P4-Q2-BX: positive bounded quadratic form of the genuine original Wilson reference

BW constructs the unique continuous real-bilinear extension of the LITERAL
mass-weighted twelve-color Wilson Haar reference to the ACTUAL physical
ground-state joint L², with the uniform mixed estimate constant 12.

This file proves full-space symmetry, continuous diagonal quadratic energy,
nonnegativity obtained from the genuine bounded Wilson concrete core by
density, its original-reference diagonal identity, the quantitative upper
bound 12, the real quadratic homogeneity and parallelogram identity, and
the two-slot quadratic difference estimate on arbitrary physical L² classes.

These are finite-volume statements about the reference form. No reverse
Wilson/Haar comparison, strict spectral gap, or continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "B" =>
  p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
local notation "Bcore" =>
  p4Q2BV_originalRangeContinuousBilin H N hN beta hbeta

/-- The full-space extension is symmetric, since its flipped bilinear form
agrees with the original symmetric Wilson form on the dense core. -/
theorem p4Q2BX_originalFullJointBilin_flip_eq :
    B.flip = B := by
  apply p4Q2BW_originalFullJointContinuousBilin_unique
    H N hN beta hbeta
  intro x y
  change B (y : J) (x : J) = Bcore x y
  rw [p4Q2BW_originalFullJointContinuousBilin_apply_range]
  rw [p4Q2BV_originalRangeContinuousBilin_apply,
      p4Q2BV_originalRangeContinuousBilin_apply]
  exact (p4Q2BV_originalRangePolarization_symm
    H N hN beta hbeta x y).symm

/-- Genuine symmetry for every pair of physical joint L² vectors. -/
theorem p4Q2BX_originalFullJointBilin_symm (x y : J) :
    B x y = B y x := by
  have h := congrArg
    (fun C : J →L[ℝ] J →L[ℝ] ℝ => C y x)
    (p4Q2BX_originalFullJointBilin_flip_eq H N hN beta hbeta)
  simpa only [ContinuousLinearMap.flip_apply] using h

/-- The reference energy of ANY physical L² vector, without choosing
pointwise representatives of its equivalence class. -/
noncomputable def p4Q2BX_originalFullJointQuadratic (x : J) : ℝ :=
  B x x

/-- Exact matching with the literal original Wilson twelve-color mass-weighted
Haar reference on the physically embedded bounded concrete core. -/
theorem p4Q2BX_originalFullJointQuadratic_on_range (x : Img) :
    p4Q2BX_originalFullJointQuadratic H N hN beta hbeta (x : J) =
      p4Q2BP_originalCoreReference H N hN beta hbeta
        (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) := by
  exact p4Q2BW_originalFullJointContinuousBilin_self_on_range
    H N hN beta hbeta x

/-- The diagonal of the continuous bilinear extension is continuous in
the actual physical joint Hilbert norm. -/
theorem p4Q2BX_originalFullJointQuadratic_continuous :
    Continuous (p4Q2BX_originalFullJointQuadratic H N hN beta hbeta : J → ℝ) := by
  change Continuous (fun x : J => B x x)
  exact B.continuous₂.comp (continuous_id.prodMk continuous_id)

/-- The extended ORIGINAL reference energy is nonnegative on the WHOLE
physical joint L². This relies on literal Wilson core positivity and
the proved density, not on a new positivity assumption. -/
theorem p4Q2BX_originalFullJointQuadratic_nonneg (x : J) :
    0 ≤ p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x := by
  have hd : DenseRange ((LinearMap.range T).subtypeL : Img →L[ℝ] J) :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  refine hd.induction_on x
    (isClosed_le continuous_const
      (p4Q2BX_originalFullJointQuadratic_continuous H N hN beta hbeta)) ?_
  intro y
  rw [p4Q2BX_originalFullJointQuadratic_on_range]
  exact p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta
    (p4Q2BV_originalCoreRepresentative H N hN beta hbeta y)

/-- The original Wilson reference has a global quadratic upper bound
with the SAME unnormalized twelve-color constant 12. -/
theorem p4Q2BX_originalFullJointQuadratic_le (x : J) :
    p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x ≤
      (12 : ℝ) * ‖x‖ ^ 2 := by
  have h := p4Q2BW_originalFullJointContinuousBilin_norm_le
    H N hN beta hbeta x x
  change ‖p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x‖ ≤
    (12 : ℝ) * ‖x‖ * ‖x‖ at h
  rw [Real.norm_eq_abs,
    abs_of_nonneg (p4Q2BX_originalFullJointQuadratic_nonneg
      H N hN beta hbeta x)] at h
  simpa only [pow_two, mul_assoc] using h

/-- True real quadratic scaling on every physical joint L² class. -/
theorem p4Q2BX_originalFullJointQuadratic_smul (a : ℝ) (x : J) :
    p4Q2BX_originalFullJointQuadratic H N hN beta hbeta (a • x) =
      a ^ 2 * p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x := by
  change B (a • x) (a • x) = a ^ 2 * B x x
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Exact parallelogram identity on the full physical joint L². -/
theorem p4Q2BX_originalFullJointQuadratic_parallelogram (x y : J) :
    p4Q2BX_originalFullJointQuadratic H N hN beta hbeta (x + y) +
      p4Q2BX_originalFullJointQuadratic H N hN beta hbeta (x - y) =
      2 * (p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x +
        p4Q2BX_originalFullJointQuadratic H N hN beta hbeta y) := by
  change B (x + y) (x + y) + B (x - y) (x - y) =
    2 * (B x x + B y y)
  simp only [map_add, map_sub, add_apply, sub_apply]
  ring

/-- Two-slot telescoping identity for the global Wilson reference
quadratic energy. No representative selection appears. -/
theorem p4Q2BX_originalFullJointQuadratic_difference (x y : J) :
    p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x -
      p4Q2BX_originalFullJointQuadratic H N hN beta hbeta y =
      B (x - y) x + B y (x - y) := by
  change B x x - B y y = B (x - y) x + B y (x - y)
  simp only [map_sub, sub_apply]
  ring

/-- The global quadratic reference is locally Lipschitz in the actual
physical joint L² norm, with no additional Wilson-measure hypothesis. -/
theorem p4Q2BX_originalFullJointQuadratic_difference_le (x y : J) :
    |p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x -
      p4Q2BX_originalFullJointQuadratic H N hN beta hbeta y| ≤
      (12 : ℝ) * ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h₁ := p4Q2BW_originalFullJointContinuousBilin_norm_le
    H N hN beta hbeta (x - y) x
  have h₂ := p4Q2BW_originalFullJointContinuousBilin_norm_le
    H N hN beta hbeta y (x - y)
  calc
    |p4Q2BX_originalFullJointQuadratic H N hN beta hbeta x -
      p4Q2BX_originalFullJointQuadratic H N hN beta hbeta y| =
        |B (x - y) x + B y (x - y)| := by
          rw [p4Q2BX_originalFullJointQuadratic_difference
            H N hN beta hbeta x y]
    _ ≤ |B (x - y) x| + |B y (x - y)| := abs_add_le _ _
    _ ≤ (12 : ℝ) * ‖x - y‖ * ‖x‖ +
        (12 : ℝ) * ‖y‖ * ‖x - y‖ :=
      add_le_add (by simpa only [Real.norm_eq_abs] using h₁)
        (by simpa only [Real.norm_eq_abs] using h₂)
    _ = (12 : ℝ) * ‖x - y‖ * (‖x‖ + ‖y‖) := by ring

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
