import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointL2Quadratic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# P4-Q2-BY: true physical joint-L² Riesz operator for the ORIGINAL Wilson Haar reference

BW constructs the unique physical Hilbert-wide continuous real bilinear
form extending the LITERAL mass-weighted original Wilson twelve-color Haar
reference. BX proves its global symmetry, positivity on the diagonal, and
the quantitative original constant-12 bound.

The existing pinned mathlib Fréchet--Riesz correspondence
`InnerProductSpace.continuousLinearMapOfBilin` now produces an ACTUAL bounded
real-linear endomorphism of the SAME original physical ground-state joint L².

Its matrix coefficients are literally the BW Wilson Haar polarization; it
is uniquely determined by those coefficients, self-adjoint, positive
semidefinite and bounded in operator norm by 12. Its diagonal is exactly
BX's full-space original Wilson reference quadratic energy.

This is NOT a lower spectral gap, reverse Wilson/Haar coercivity, volume-
uniform continuum generator estimate, or a proof of Yang--Mills mass gap.
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

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "B" =>
  p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta

/-- The ORIGINAL twelve-color Wilson Haar reference realizes a genuine
bounded physical ground-state joint L² operator by Fréchet--Riesz. -/
noncomputable def p4Q2BY_originalFullJointRieszOperator : J →L[ℝ] J :=
  InnerProductSpace.continuousLinearMapOfBilin
    (𝕜 := ℝ) (p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta)

/-- The Riesz operator's matrix coefficients are EXACTLY the original
mass-weighted Wilson reference polarization for arbitrary joint L² classes. -/
theorem p4Q2BY_originalFullJointRieszOperator_inner
    (x y : J) :
    inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) y =
      B x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply B x y

/-- Unique bounded operator representing the full original Wilson Haar
reference form: equality of all Hilbert matrix elements determines it. -/
theorem p4Q2BY_originalFullJointRieszOperator_unique
    (other : J →L[ℝ] J)
    (hother : ∀ x y : J, inner ℝ (other x) y = B x y) :
    other = p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  calc
    inner ℝ (other x) y = B x y := hother x y
    _ = inner ℝ (p4Q2BY_originalFullJointRieszOperator
        H N hN beta hbeta x) y :=
      (p4Q2BY_originalFullJointRieszOperator_inner H N hN beta hbeta x y).symm

/-- The Riesz operator is genuinely self-adjoint in the physical Hilbert
inner product, as the original Wilson polarization is symmetric on ALL L². -/
theorem p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint :
    IsSelfAdjoint (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2
  intro x y
  change inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) y =
    inner ℝ x (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta y)
  calc
    inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) y =
        B x y :=
      p4Q2BY_originalFullJointRieszOperator_inner H N hN beta hbeta x y
    _ = B y x := p4Q2BX_originalFullJointBilin_symm H N hN beta hbeta x y
    _ = inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta y) x :=
      (p4Q2BY_originalFullJointRieszOperator_inner H N hN beta hbeta y x).symm
    _ = inner ℝ x (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta y) :=
      real_inner_comm _ _

/-- The original Wilson Riesz operator exactly represents BX's full
joint-L² reference quadratic energy. -/
theorem p4Q2BY_originalFullJointRieszOperator_quadratic (x : J) :
    inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) x =
      Q x :=
  p4Q2BY_originalFullJointRieszOperator_inner H N hN beta hbeta x x

/-- Positive semidefinite action on every actual physical Wilson joint
Hilbert class, without inventing a lower coercivity estimate. -/
theorem p4Q2BY_originalFullJointRieszOperator_inner_nonneg (x : J) :
    0 ≤ inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) x := by
  rw [p4Q2BY_originalFullJointRieszOperator_quadratic]
  exact p4Q2BX_originalFullJointQuadratic_nonneg H N hN beta hbeta x

/-- The quadratic operator upper bound inherits exactly the original
unnormalized twelve-color coefficient. -/
theorem p4Q2BY_originalFullJointRieszOperator_inner_le (x : J) :
    inner ℝ (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x) x ≤
      (12 : ℝ) * ‖x‖ ^ 2 := by
  rw [p4Q2BY_originalFullJointRieszOperator_quadratic]
  exact p4Q2BX_originalFullJointQuadratic_le H N hN beta hbeta x

/-- Fréchet--Riesz preserves the norm of the original Wilson functional
in each input vector of the true physical Hilbert space. -/
theorem p4Q2BY_originalFullJointRieszOperator_norm_eq_dual (x : J) :
    ‖p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x‖ =
      ‖B x‖ := by
  change ‖(InnerProductSpace.toDual ℝ J).symm (B x)‖ = ‖B x‖
  exact (InnerProductSpace.toDual ℝ J).symm.norm_map (B x)

/-- The original Wilson reference Riesz operator is bounded in operator
norm by 12 on the WHOLE physical joint L², not just a bounded core. -/
theorem p4Q2BY_originalFullJointRieszOperator_opNorm_le :
    ‖p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta‖ ≤
      (12 : ℝ) := by
  have hDual (x : J) : ‖B x‖ ≤ (12 : ℝ) * ‖x‖ := by
    refine (B x).opNorm_le_bound (mul_nonneg (by norm_num) (norm_nonneg x)) ?_
    intro y
    simpa only [mul_assoc] using
      (p4Q2BW_originalFullJointContinuousBilin_norm_le H N hN beta hbeta x y)
  refine (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta).opNorm_le_bound
    (by norm_num) ?_
  intro x
  calc
    ‖p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta x‖ = ‖B x‖ :=
      p4Q2BY_originalFullJointRieszOperator_norm_eq_dual H N hN beta hbeta x
    _ ≤ (12 : ℝ) * ‖x‖ := hDual x

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
