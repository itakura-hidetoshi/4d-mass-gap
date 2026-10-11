import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRealPolarization
import Mathlib.Tactic

/-!
# P4-Q2-BP: original Wilson real polarization is biadditive on the physical bounded core

BN proves the literal mass-weighted original Wilson twelve-color real
reference satisfies the parallelogram law for bounded strongly measurable
concrete original joint observables. BO defined the symmetric, diagonal-exact
real polarization of that same original reference.

This file organizes those observables into their genuine real submodule,
proves the parallelogram law INSIDE the submodule, and applies an abstract
additive-group argument to obtain polar ADDITIVITY in both variables.

The abstract calculation is Jensen's identity for the polarization,
plus the evenness of the quadratic energy. No additive property is silently
inferred from scalar homogeneity, and no quadratic surrogate is introduced.

This proves biadditivity, not yet arbitrary REAL homogeneity, continuous
bilinearity or representative-independent descent to all physical joint L².
There is no reverse reference Poincare or continuum mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 1600000

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

/-- Algebraic polarization of an arbitrary real-valued function on an
abelian additive group. No bilinearity is assumed in this definition. -/
noncomputable def p4Q2BP_abstractPolarization
    {E : Type*} [AddCommGroup E] (Q : E → ℝ) (x y : E) : ℝ :=
  (Q (x + y) - Q (x - y)) / 4

/-- The polarized Jensen identity follows from just TWO instances of
the parallelogram law. This is the central algebraic step. -/
theorem p4Q2BP_abstractPolarization_jensen
    {E : Type*} [AddCommGroup E] (Q : E → ℝ)
    (x z y : E)
    (hPlus :
      Q ((x + y) + z) + Q ((x + y) - z) =
        2 * (Q (x + y) + Q z))
    (hMinus :
      Q ((x - y) + z) + Q ((x - y) - z) =
        2 * (Q (x - y) + Q z)) :
    p4Q2BP_abstractPolarization Q (x + z) y +
      p4Q2BP_abstractPolarization Q (x - z) y =
        2 * p4Q2BP_abstractPolarization Q x y := by
  have hpA : (x + z) + y = (x + y) + z := by abel
  have hpB : (x + z) - y = (x - y) + z := by abel
  have hmA : (x - z) + y = (x + y) - z := by abel
  have hmB : (x - z) - y = (x - y) - z := by abel
  unfold p4Q2BP_abstractPolarization
  rw [hpA, hpB, hmA, hmB]
  linarith [hPlus, hMinus]

/-- Evenness of Q makes its polarization odd in the first input. -/
theorem p4Q2BP_abstractPolarization_neg_left
    {E : Type*} [AddCommGroup E] (Q : E → ℝ)
    (hEven : ∀ v : E, Q (-v) = Q v)
    (x y : E) :
    p4Q2BP_abstractPolarization Q (-x) y =
      -p4Q2BP_abstractPolarization Q x y := by
  have hp : (-x) + y = -(x - y) := by abel
  have hm : (-x) - y = -(x + y) := by abel
  unfold p4Q2BP_abstractPolarization
  rw [hp, hm, hEven (x - y), hEven (x + y)]
  ring

/-- Parallelogram law and evenness imply polar ADDITIVITY.
This theorem is valid for any real-valued Q on an abelian group,
without imposing or claiming real scalar linearity. -/
theorem p4Q2BP_abstractPolarization_add_left
    {E : Type*} [AddCommGroup E] (Q : E → ℝ)
    (hPara : ∀ x y : E,
      Q (x + y) + Q (x - y) = 2 * (Q x + Q y))
    (hEven : ∀ v : E, Q (-v) = Q v)
    (x z y : E) :
    p4Q2BP_abstractPolarization Q (x + z) y =
      p4Q2BP_abstractPolarization Q x y +
        p4Q2BP_abstractPolarization Q z y := by
  have hj1 :=
    p4Q2BP_abstractPolarization_jensen Q x z y
      (hPara (x + y) z) (hPara (x - y) z)
  have hj2 :=
    p4Q2BP_abstractPolarization_jensen Q z x y
      (hPara (z + y) x) (hPara (z - y) x)
  have hzx : z + x = x + z := by abel
  have hdiff : z - x = -(x - z) := by abel
  rw [hzx, hdiff,
    p4Q2BP_abstractPolarization_neg_left Q hEven (x - z) y] at hj2
  linarith

section OriginalWilson

variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg

/-- Real submodule of all bounded, strongly measurable ORIGINAL concrete
Wilson joint functions. This is a genuine linear core, not an invented
measure or a replacement for physical joint L². -/
def p4Q2BP_originalBoundedStronglyMeasurableCore :
    Submodule ℝ (Joint → ℝ) where
  carrier := {F | StronglyMeasurable F ∧
    ∃ b : ℝ, ∀ z, ‖F z‖ ≤ b}
  zero_mem' := by
    constructor
    · exact stronglyMeasurable_const
    · refine ⟨0, ?_⟩
      intro z
      simp
  add_mem' := by
    intro F G hF hG
    rcases hF with ⟨hFm, ⟨bF, hbF⟩⟩
    rcases hG with ⟨hGm, ⟨bG, hbG⟩⟩
    constructor
    · exact hFm.add hGm
    · refine ⟨bF + bG, ?_⟩
      intro z
      exact (norm_add_le (F z) (G z)).trans
        (add_le_add (hbF z) (hbG z))
  smul_mem' := by
    intro a F hF
    rcases hF with ⟨hFm, ⟨bF, hbF⟩⟩
    constructor
    · change StronglyMeasurable (fun z => a * F z)
      exact hFm.const_mul a
    · refine ⟨‖a‖ * bF, ?_⟩
      intro z
      change ‖a • F z‖ ≤ ‖a‖ * bF
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbF z) (norm_nonneg a)

variable (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

/-- The literal original physical Wilson reference restricted to its
bounded strongly measurable concrete joint core. -/
noncomputable def p4Q2BP_originalCoreReference
    (F : p4Q2BP_originalBoundedStronglyMeasurableCore H N) : ℝ :=
  p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
    H N hN beta hbeta F.1

/-- The REAL physical original reference satisfies parallelogram law on
the entire bounded strongly measurable submodule. -/
theorem p4Q2BP_originalCoreReference_parallelogram
    (F G : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalCoreReference H N hN beta hbeta (F + G) +
      p4Q2BP_originalCoreReference H N hN beta hbeta (F - G) =
        2 * (p4Q2BP_originalCoreReference H N hN beta hbeta F +
          p4Q2BP_originalCoreReference H N hN beta hbeta G) := by
  rcases F.property with ⟨hF, ⟨bF, hbF⟩⟩
  rcases G.property with ⟨hG, ⟨bG, hbG⟩⟩
  have h := p4Q2BN_originalWilsonTwelveColorHaarReferenceReal_parallelogram
    H N hN beta hbeta F.1 G.1 hF hG bF hbF bG hbG
  simpa only [p4Q2BP_originalCoreReference, Submodule.coe_add,
    Submodule.coe_sub, Pi.add_apply, Pi.sub_apply] using h

/-- Evenness holds in the SAME original bounded joint core. -/
theorem p4Q2BP_originalCoreReference_even
    (F : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalCoreReference H N hN beta hbeta (-F) =
      p4Q2BP_originalCoreReference H N hN beta hbeta F := by
  change
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta (fun z => -F.1 z) =
    p4Q2BD_originalWilsonTwelveColorHaarReferenceReal
      H N hN beta hbeta F.1
  exact p4Q2BO_originalWilsonReference_neg H N hN beta hbeta F.1

/-- Actual BO polarization on the bounded original Wilson core.
The partial, unrestricted concrete polarization remains BO's definition. -/
noncomputable def p4Q2BP_originalCorePolarization
    (F G : p4Q2BP_originalBoundedStronglyMeasurableCore H N) : ℝ :=
  p4Q2BO_originalWilsonRealPolarization H N hN beta hbeta F.1 G.1

/-- The original Wilson core polarization is ADDITIVE in the first
variable. This is genuine algebraic progress toward ℝ-bilinearity. -/
theorem p4Q2BP_originalCorePolarization_add_left
    (F G K : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalCorePolarization H N hN beta hbeta (F + G) K =
      p4Q2BP_originalCorePolarization H N hN beta hbeta F K +
        p4Q2BP_originalCorePolarization H N hN beta hbeta G K := by
  change
    p4Q2BP_abstractPolarization
      (p4Q2BP_originalCoreReference H N hN beta hbeta) (F + G) K =
      p4Q2BP_abstractPolarization
        (p4Q2BP_originalCoreReference H N hN beta hbeta) F K +
      p4Q2BP_abstractPolarization
        (p4Q2BP_originalCoreReference H N hN beta hbeta) G K
  exact p4Q2BP_abstractPolarization_add_left
    (p4Q2BP_originalCoreReference H N hN beta hbeta)
    (p4Q2BP_originalCoreReference_parallelogram H N hN beta hbeta)
    (p4Q2BP_originalCoreReference_even H N hN beta hbeta)
    F G K

/-- BO's proved symmetry holds unchanged on the actual bounded core. -/
theorem p4Q2BP_originalCorePolarization_symm
    (F G : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalCorePolarization H N hN beta hbeta F G =
      p4Q2BP_originalCorePolarization H N hN beta hbeta G F :=
  p4Q2BO_originalWilsonRealPolarization_symm
    H N hN beta hbeta F.1 G.1

/-- Additivity in the second variable follows from the true BO symmetry,
rather than an assumed separate original-fiber independence. -/
theorem p4Q2BP_originalCorePolarization_add_right
    (F G K : p4Q2BP_originalBoundedStronglyMeasurableCore H N) :
    p4Q2BP_originalCorePolarization H N hN beta hbeta F (G + K) =
      p4Q2BP_originalCorePolarization H N hN beta hbeta F G +
        p4Q2BP_originalCorePolarization H N hN beta hbeta F K := by
  calc
    p4Q2BP_originalCorePolarization H N hN beta hbeta F (G + K) =
        p4Q2BP_originalCorePolarization H N hN beta hbeta (G + K) F :=
      p4Q2BP_originalCorePolarization_symm H N hN beta hbeta F (G + K)
    _ = p4Q2BP_originalCorePolarization H N hN beta hbeta G F +
          p4Q2BP_originalCorePolarization H N hN beta hbeta K F :=
      p4Q2BP_originalCorePolarization_add_left H N hN beta hbeta G K F
    _ = p4Q2BP_originalCorePolarization H N hN beta hbeta F G +
          p4Q2BP_originalCorePolarization H N hN beta hbeta F K := by
      rw [p4Q2BP_originalCorePolarization_symm H N hN beta hbeta G F,
          p4Q2BP_originalCorePolarization_symm H N hN beta hbeta K F]

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
