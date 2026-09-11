import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2CompatibleOperatorExtension
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderDensity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Every typed Euclidean Yang--Mills projective-limit measure is locally
available as a probability measure throughout this operator-extension
specialization file. -/
local instance projectiveLimitContinuumProbabilityForOperatorExtension
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

/-- A uniformly bounded compatible operator family on the finite-dimensional
`L²` marginals of one Euclidean Yang--Mills projective-limit measure. -/
abbrev EuclideanYangMillsProjectiveLimitL2OperatorSystem
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :=
  ProjectiveLimitFiniteMarginalL2OperatorSystem
    L.continuumMeasure F.finiteMarginal L.projectiveLimit F.projective

namespace EuclideanYangMillsProjectiveLimitMeasure

variable
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- The algebraic dense cylinder-core operator canonically glued from one
compatible Euclidean Yang--Mills finite-marginal operator system. -/
noncomputable def finiteMarginalL2CylinderCoreOperator
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L) :
    L.finiteMarginalL2CylinderTotalSubspace →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  S.cylinderCoreOperator

/-- The canonical bounded continuum `L²` operator obtained by extending the
glued finite-marginal cylinder-core operator. -/
noncomputable def finiteMarginalL2ContinuumOperator
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L) :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  S.continuumOperator

/-- The Euclidean Yang--Mills continuum operator agrees exactly with the glued
operator on the dense algebraic finite-coordinate cylinder core. -/
theorem finiteMarginalL2ContinuumOperator_apply_core
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L)
    (x : L.finiteMarginalL2CylinderTotalSubspace) :
    L.finiteMarginalL2ContinuumOperator S
        (x : Lp ℝ 2 L.continuumMeasure) =
      L.finiteMarginalL2CylinderCoreOperator S x := by
  exact S.continuumOperator_apply_core x

/-- Exact finite-to-continuum intertwining for every Euclidean Yang--Mills
finite marginal. -/
theorem finiteMarginalL2ContinuumOperator_intertwines
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L)
    (J : Finset EuclideanFourSpace)
    (f : Lp ℝ 2 (F.finiteMarginal J)) :
    L.finiteMarginalL2ContinuumOperator S
        (L.finiteMarginalL2Pullback J f) =
      L.finiteMarginalL2Pullback J (S.localOperator J f) := by
  exact S.continuumOperator_intertwines_finite J f

/-- The common finite-marginal pointwise norm bound survives on the full
continuum projective-limit `L²` carrier. -/
theorem finiteMarginalL2ContinuumOperator_norm_le
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L)
    (x : Lp ℝ 2 L.continuumMeasure) :
    ‖L.finiteMarginalL2ContinuumOperator S x‖ ≤
      S.bound * ‖x‖ := by
  exact S.continuumOperator_norm_le x

/-- The continuum operator norm is bounded by the same common finite-marginal
constant. -/
theorem finiteMarginalL2ContinuumOperator_opNorm_le
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L) :
    ‖L.finiteMarginalL2ContinuumOperator S‖ ≤ S.bound := by
  exact S.continuumOperator_opNorm_le

/-- The canonical continuum extension is uniquely characterized among bounded
operators by its exact intertwining with every finite marginal embedding. -/
theorem finiteMarginalL2ContinuumOperator_unique
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L)
    (g : Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure)
    (hg : ∀ (J : Finset EuclideanFourSpace)
      (f : Lp ℝ 2 (F.finiteMarginal J)),
      g (L.finiteMarginalL2Pullback J f) =
        L.finiteMarginalL2Pullback J (S.localOperator J f)) :
    L.finiteMarginalL2ContinuumOperator S = g := by
  exact S.continuumOperator_unique g hg

end EuclideanYangMillsProjectiveLimitMeasure

/-- Audit-visible Euclidean Yang--Mills receipt for the complete route from a
compatible uniformly bounded family of finite-marginal `L²` operators to one
unique bounded continuum projective-limit `L²` operator. -/
structure EuclideanYangMillsProjectiveLimitL2OperatorExtensionPackage
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  system : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L
  cylinderCoreOperator :
    L.finiteMarginalL2CylinderTotalSubspace →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure
  continuumOperator :
    Lp ℝ 2 L.continuumMeasure →L[ℝ]
      Lp ℝ 2 L.continuumMeasure
  coreAgreement :
    ∀ x : L.finiteMarginalL2CylinderTotalSubspace,
      continuumOperator (x : Lp ℝ 2 L.continuumMeasure) =
        cylinderCoreOperator x
  finiteIntertwining :
    ∀ (J : Finset EuclideanFourSpace)
      (f : Lp ℝ 2 (F.finiteMarginal J)),
      continuumOperator (L.finiteMarginalL2Pullback J f) =
        L.finiteMarginalL2Pullback J (system.localOperator J f)
  continuumNormBound :
    ∀ x : Lp ℝ 2 L.continuumMeasure,
      ‖continuumOperator x‖ ≤ system.bound * ‖x‖
  continuumOpNormBound :
    ‖continuumOperator‖ ≤ system.bound
  uniqueness :
    ∀ g : Lp ℝ 2 L.continuumMeasure →L[ℝ]
        Lp ℝ 2 L.continuumMeasure,
      (∀ (J : Finset EuclideanFourSpace)
        (f : Lp ℝ 2 (F.finiteMarginal J)),
        g (L.finiteMarginalL2Pullback J f) =
          L.finiteMarginalL2Pullback J (system.localOperator J f)) →
      continuumOperator = g

/-- Construct the complete Euclidean Yang--Mills finite-marginal operator
extension receipt from one compatible uniformly bounded operator system. -/
noncomputable def euclideanYangMillsProjectiveLimitL2OperatorExtensionPackage
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (S : EuclideanYangMillsProjectiveLimitL2OperatorSystem F L) :
    EuclideanYangMillsProjectiveLimitL2OperatorExtensionPackage F L where
  system := S
  cylinderCoreOperator := L.finiteMarginalL2CylinderCoreOperator S
  continuumOperator := L.finiteMarginalL2ContinuumOperator S
  coreAgreement := L.finiteMarginalL2ContinuumOperator_apply_core S
  finiteIntertwining := L.finiteMarginalL2ContinuumOperator_intertwines S
  continuumNormBound := L.finiteMarginalL2ContinuumOperator_norm_le S
  continuumOpNormBound := L.finiteMarginalL2ContinuumOperator_opNorm_le S
  uniqueness := L.finiteMarginalL2ContinuumOperator_unique S

end

end MathlibAnalytic
end MGAP4D
