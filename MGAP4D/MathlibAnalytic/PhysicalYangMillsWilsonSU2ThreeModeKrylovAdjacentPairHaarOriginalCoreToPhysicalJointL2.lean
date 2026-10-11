import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRealPolarizationBilinearCore
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# P4-Q2-BR: linear quotient map for actual original Wilson bounded joint cores

BQ constructs a true REAL bilinear polarization of the literal Wilson
mass-weighted twelve-color Haar reference on the bounded strongly
measurable physical joint-observable core.

BR connects that concrete core to the ACTUAL original Wilson ground-state
joint L² quotient. All functions in the core are MemLp for the existing
physical joint law. Their canonical toLp construction is real-linear,
and the underlying core reference obeys the all-beta domination
Q(F) ≤ 12 * ‖toPhysicalL2(F)‖². Consequently Q(F)=0 for every concrete
core observable representing the zero physical joint L² class.

No artificial probability law, fiber mass floor, positive beta cutoff,
new axiom, or continuum-mass-gap claim is introduced. The next goal
is to prove annihilation of the kernel by the actual Wilson polarization,
and hence representative-independent descent.
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

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "μ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "Q" =>
  p4Q2BP_originalCoreReference H N hN beta hbeta

/-- Every member of the actual bounded original Wilson concrete core is
square-integrable for the ACTUAL physical ground-state joint measure. -/
theorem p4Q2BR_originalCore_memLp
    (F : Core) : MemLp (F : Joint → ℝ) 2 μ := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_memLp_two
      H N hN beta hbeta F.1 hF bound hbound

/-- Canonical actual Wilson physical joint L² representative of a core
observable; no pointwise evaluation of the quotient is used. -/
noncomputable def p4Q2BR_originalCorePhysicalL2
    (F : Core) : J :=
  (p4Q2BR_originalCore_memLp H N hN beta hbeta F).toLp F.1

/-- True additivity of the canonical original Wilson concrete-to-L² map,
using pinned mathlib MemLp.toLp_add and proof irrelevance. -/
theorem p4Q2BR_originalCorePhysicalL2_add
    (F G : Core) :
    p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta (F + G) =
      p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta F +
        p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta G := by
  change
    (p4Q2BR_originalCore_memLp H N hN beta hbeta (F + G)).toLp
      (F.1 + G.1) =
    (p4Q2BR_originalCore_memLp H N hN beta hbeta F).toLp F.1 +
      (p4Q2BR_originalCore_memLp H N hN beta hbeta G).toLp G.1
  exact
    MemLp.toLp_add
      (p4Q2BR_originalCore_memLp H N hN beta hbeta F)
      (p4Q2BR_originalCore_memLp H N hN beta hbeta G)

/-- Actual Wilson quotient representation commutes with all real scalars. -/
theorem p4Q2BR_originalCorePhysicalL2_smul
    (a : ℝ) (F : Core) :
    p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta (a • F) =
      a • p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta F := by
  change
    (p4Q2BR_originalCore_memLp H N hN beta hbeta (a • F)).toLp
      (a • F.1) =
    a • (p4Q2BR_originalCore_memLp H N hN beta hbeta F).toLp F.1
  exact
    MemLp.toLp_const_smul a
      (p4Q2BR_originalCore_memLp H N hN beta hbeta F)

/-- The concrete core-to-physical-joint-L² map is an actual real-linear map,
not merely a statement about representatives. -/
noncomputable def p4Q2BR_originalCoreToPhysicalL2Linear :
    Core →ₗ[ℝ] J where
  toFun := p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta
  map_add' := p4Q2BR_originalCorePhysicalL2_add H N hN beta hbeta
  map_smul' := p4Q2BR_originalCorePhysicalL2_smul H N hN beta hbeta

/-- The core linear map is EXACTLY the prior AZ bounded concrete vector,
independent of the particular bound witness used in the construction. -/
theorem p4Q2BR_originalCorePhysicalL2_eq_originalAZ
    (F : Core)
    (hF : StronglyMeasurable (F : Joint → ℝ))
    (bound : ℝ) (hbound : ∀ z, ‖F.1 z‖ ≤ bound) :
    p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta F =
      p4Q2AZ_originalJointL2 H N hN beta hbeta F.1 hF bound hbound := by
  rfl

/-- Crucial cutoff-free genuine physical norm domination of the ORIGINAL
mass-weighted Wilson twelve-color Haar quadratic energy on the bounded core.
The coefficient 12 is the existing unnormalized twelve-color convention. -/
theorem p4Q2BR_originalCoreReference_le_physicalL2_normSq
    (F : Core) :
    Q F ≤ (12 : ℝ) *
      ‖p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta F‖ ^ 2 := by
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have h :=
    p4Q2BE_originalWilsonReferenceReal_le_twelve_jointNormSq
      H N hN beta hbeta F.1 hF bound hbound
  rw [← p4Q2BR_originalCorePhysicalL2_eq_originalAZ
    H N hN beta hbeta F hF bound hbound] at h
  exact h

/-- The zero vector of the ACTUAL physical joint L² quotient lies in the
radical of the quadratic energy on the original concrete Wilson core. -/
theorem p4Q2BR_originalCoreReference_eq_zero_of_physicalL2_zero
    (F : Core)
    (hzero : p4Q2BR_originalCorePhysicalL2
      H N hN beta hbeta F = 0) :
    Q F = 0 := by
  have hnonneg :=
    p4Q2BQ_originalCoreReference_nonneg H N hN beta hbeta F
  have hupper :=
    p4Q2BR_originalCoreReference_le_physicalL2_normSq
      H N hN beta hbeta F
  rw [hzero, norm_zero] at hupper
  exact le_antisymm (by nlinarith) hnonneg

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
