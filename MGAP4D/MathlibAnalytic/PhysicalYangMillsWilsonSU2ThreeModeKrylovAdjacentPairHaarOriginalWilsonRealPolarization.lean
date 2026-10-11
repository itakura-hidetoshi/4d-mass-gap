import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorParallelogram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGroundStateTwelveColorCenteredVarianceBound
import Mathlib.Tactic

/-!
# P4-Q2-BO: algebraic polarization of the REAL original Wilson reference

BH/BI prove scalar quadratic homogeneity for the original Wilson mass-weighted
twelve-color Haar reference; BN proves its real parallelogram law on the
bounded strongly measurable concrete joint core. This file constructs the
ordinary real polarization expression (Q(F+G)-Q(F-G))/4 and establishes
its symmetry, exact diagonal Q(F), and nonnegative diagonal.

These identities require NO new physical measure, fiber mass floor, or
high-temperature premise. On bounded original concrete joint observables,
the diagonal remains controlled above by the TRUE centered physical joint
L² variance using BF.

CAUTION: polarization symmetry and diagonal equality alone are NOT a
complete proof of additivity or ℝ-linearity in either variable. That
requires further use of the parallelogram law on a closed bounded core,
and the separate quotient well-definedness proof remains open.
This file does not assert a bilinear form or a continuum mass gap.
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
local notation "Q" =>
  p4Q2BD_originalWilsonTwelveColorHaarReferenceReal H N hN beta hbeta

/-- Explicit algebraic polarization of the LITERAL original Wilson
twelve-color mass-weighted Haar reference on concrete joint functions.
This definition itself does not assert bilinearity. -/
noncomputable def p4Q2BO_originalWilsonRealPolarization
    (F G : Joint → ℝ) : ℝ :=
  (Q (fun z => F z + G z) - Q (fun z => F z - G z)) / 4

/-- Actual original twelve-color Wilson real reference at zero vanishes,
using the pre-existing all-beta scalar quadratic law. -/
theorem p4Q2BO_originalWilsonReference_zero :
    Q (fun _ : Joint => (0 : ℝ)) = 0 := by
  have h :=
    p4Q2BI_originalWilsonTwelveColorHaarReferenceReal_mul
      H N hN beta hbeta (0 : ℝ) (fun _ : Joint => (0 : ℝ))
  simpa using h

/-- Quadratic scalar law yields evenness for the ACTUAL original Wilson
reference, without any bounded-core assumption. -/
theorem p4Q2BO_originalWilsonReference_neg
    (F : Joint → ℝ) :
    Q (fun z => -F z) = Q F := by
  have h :=
    p4Q2BI_originalWilsonTwelveColorHaarReferenceReal_mul
      H N hN beta hbeta (-1 : ℝ) F
  simpa [pow_two] using h

/-- Commutativity under the sum of concrete original observables. -/
theorem p4Q2BO_originalWilsonReference_add_comm
    (F G : Joint → ℝ) :
    Q (fun z => F z + G z) = Q (fun z => G z + F z) := by
  have hfn :
      (fun z : Joint => F z + G z) =
        (fun z : Joint => G z + F z) := by
    funext z
    ac_rfl
  exact congrArg Q hfn

/-- The reference cannot distinguish F-G from G-F because it is even. -/
theorem p4Q2BO_originalWilsonReference_sub_flip
    (F G : Joint → ℝ) :
    Q (fun z => F z - G z) = Q (fun z => G z - F z) := by
  have hfn :
      (fun z : Joint => F z - G z) =
        (fun z : Joint => -(G z - F z)) := by
    funext z
    ring
  rw [hfn]
  exact p4Q2BO_originalWilsonReference_neg
    H N hN beta hbeta (fun z => G z - F z)

/-- Exact symmetry of the polarization of the ORIGINAL Wilson real reference. -/
theorem p4Q2BO_originalWilsonRealPolarization_symm
    (F G : Joint → ℝ) :
    p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta F G =
      p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta G F := by
  unfold p4Q2BO_originalWilsonRealPolarization
  rw [p4Q2BO_originalWilsonReference_add_comm
    H N hN beta hbeta F G,
    p4Q2BO_originalWilsonReference_sub_flip
      H N hN beta hbeta F G]

/-- The polarized REAL reference recovers its ACTUAL original Wilson
quadratic energy on the diagonal, for every concrete observable. -/
theorem p4Q2BO_originalWilsonRealPolarization_self
    (F : Joint → ℝ) :
    p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta F F =
      Q F := by
  have hdouble :
      (fun z : Joint => F z + F z) = (fun z => (2 : ℝ) * F z) := by
    funext z
    ring
  have hzero :
      (fun z : Joint => F z - F z) = (fun _ => (0 : ℝ)) := by
    funext z
    ring
  unfold p4Q2BO_originalWilsonRealPolarization
  rw [hdouble, hzero,
    p4Q2BI_originalWilsonTwelveColorHaarReferenceReal_mul
      H N hN beta hbeta (2 : ℝ) F,
    p4Q2BO_originalWilsonReference_zero H N hN beta hbeta]
  ring

/-- The original mass-weighted Haar reference polarization has a
nonnegative diagonal. This follows from its genuine ENNReal source. -/
theorem p4Q2BO_originalWilsonRealPolarization_self_nonneg
    (F : Joint → ℝ) :
    0 ≤ p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta F F := by
  rw [p4Q2BO_originalWilsonRealPolarization_self]
  unfold p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
  exact ENNReal.toReal_nonneg

/-- On bounded original Wilson concrete cores, the diagonal polarization
obeys the already-proved BF TRUE constant-centered variance upper bound.
This still does NOT establish a reverse reference-energy Poincare bound. -/
theorem p4Q2BO_originalWilsonRealPolarization_self_le_centeredVariance
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta F F ≤
      (12 : ℝ) *
        ‖p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
            H N hN beta hbeta
              (p4Q2AZ_originalJointL2 H N hN beta hbeta F hF bound hbound)‖ ^ 2 := by
  rw [p4Q2BO_originalWilsonRealPolarization_self]
  exact p4Q2BF_originalWilsonReferenceReal_le_twelve_centeredVariance
    H N hN beta hbeta F hF bound hbound

end
end

end MathlibAnalytic
end MGAP4D
