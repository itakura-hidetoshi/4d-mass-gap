import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonMarkovTruncationContraction
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# P4-Q2-CN: original Wilson Markov truncation on the WHOLE physical joint L²

CM proved the LITERAL original mass-weighted 12-color Wilson Haar reference
contracts under pointwise clipping for any bounded, strongly measurable
concrete observable. The actual bounded core is dense in the genuine physical
Wilson joint Hilbert L², and BW/BX already constructed its unique continuous
full-L² quadratic reference.

We use PINNED mathlib's nonlinear LipschitzWith.compLp construction to
lift clipping to the ORIGINAL joint L² equivalence classes, prove it agrees
exactly on bounded concrete vectors, and use density + continuity to obtain:

    Q_W(clip_M x) ≤ Q_W(x)    for every original physical joint L² x.

By positivity this also proves that the genuine original Wilson Riesz
operator kernel is stable under EVERY symmetric Markov clipping.

This is a full-L² nonlinear contraction, not a uniform positive gap.
The remaining obstruction to ker(A_W)=the physical constant line is
showing clipped L² kernel elements are represented by bounded concrete
observables. No such representation is tacitly assumed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2400000
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
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta
local notation "W" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "muPhys" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta

/-- Genuine nonlinear symmetric clipping on physical Wilson joint L²
equivalence classes, obtained from pinned mathlib's 1-Lipschitz compLp.
This does NOT evaluate representatives at exceptional points. -/
noncomputable def p4Q2CN_truncatePhysicalL2
    (M : ℝ) (hM : 0 ≤ M) : J → J :=
  (p4Q2CM_truncate_lipschitz M).compLp (p4Q2CM_truncate_zero M hM)

/-- Global Lipschitz continuity of the nonlinear clipping on the SAME
physical joint Hilbert L². -/
theorem p4Q2CN_truncatePhysicalL2_continuous
    (M : ℝ) (hM : 0 ≤ M) :
    Continuous (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM : J → J) :=
  (p4Q2CM_truncate_lipschitz M).continuous_compLp
    (p4Q2CM_truncate_zero M hM)

/-- The nonlinear compLp operation is a.e. the literal clipped original
joint L² representative, with no redefinition of the Wilson law. -/
theorem p4Q2CN_truncatePhysicalL2_coeFn
    (M : ℝ) (hM : 0 ≤ M) (x : J) :
    (fun z : Joint =>
      (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x) z)
      =ᵐ[muPhys]
      (fun z : Joint => p4Q2CM_truncate M (x z)) := by
  simpa only [p4Q2CN_truncatePhysicalL2, Function.comp_def] using
    ((p4Q2CM_truncate_lipschitz M).coeFn_compLp
      (p4Q2CM_truncate_zero M hM) x)

/-- On EVERY literal original bounded concrete Wilson observable, the
new nonlinear full-L² clipping is precisely the physical L² image of CM's
bounded concrete clipping; this is an equality of genuine L² classes. -/
theorem p4Q2CN_truncatePhysicalL2_eq_boundedCore
    (M : ℝ) (hM : 0 ≤ M) (F : Core) :
    p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM (T F) =
      T (p4Q2CM_truncateCore H N M hM F) := by
  apply Lp.ext
  have hc :=
    p4Q2CN_truncatePhysicalL2_coeFn
      H N hN beta hbeta M hM (T F)
  have hF :=
    p4Q2CL_originalBoundedCoreToPhysical_coeFn H N hN beta hbeta F
  have hClip :=
    p4Q2CL_originalBoundedCoreToPhysical_coeFn
      H N hN beta hbeta (p4Q2CM_truncateCore H N M hM F)
  filter_upwards [hc, hF, hClip] with z hcz hFz hClipz
  calc
    (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM (T F)) z =
        p4Q2CM_truncate M ((T F : J) z) := hcz
    _ = p4Q2CM_truncate M (F.1 z) := by rw [hFz]
    _ = (p4Q2CM_truncateCore H N M hM F).1 z := rfl
    _ = (T (p4Q2CM_truncateCore H N M hM F) : J) z := hClipz.symm

/-- MAIN CN THEOREM: unconditional Markov contraction of the LITERAL
original Wilson 12-color reference Q on ALL actual physical joint L²
classes, not merely on the bounded concrete core. It is obtained by
continuous descent of the already-proved CM inequality. -/
theorem p4Q2CN_originalFullJointQuadratic_truncate_le
    (M : ℝ) (hM : 0 ≤ M) (x : J) :
    Q (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x) ≤ Q x := by
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  refine hd.induction_on x
    (isClosed_le
      ((p4Q2BX_originalFullJointQuadratic_continuous
          H N hN beta hbeta).comp
        (p4Q2CN_truncatePhysicalL2_continuous
          H N hN beta hbeta M hM))
      (p4Q2BX_originalFullJointQuadratic_continuous H N hN beta hbeta)) ?_
  intro y
  let F : Core :=
    p4Q2BV_originalCoreRepresentative H N hN beta hbeta y
  have hy : T F = (y : J) :=
    p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta y
  have hTrunc :
      p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM (y : J) =
        T (p4Q2CM_truncateCore H N M hM F) := by
    rw [← hy]
    exact p4Q2CN_truncatePhysicalL2_eq_boundedCore
      H N hN beta hbeta M hM F
  change Q (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM (y : J)) ≤
    Q (y : J)
  rw [hTrunc, ← hy, p4Q2CL_originalFullQuadratic_eq_literalCore,
    p4Q2CL_originalFullQuadratic_eq_literalCore]
  exact p4Q2CM_originalBoundedCoreMarkov_truncate_le
    H N hN beta hbeta M hM F

/-- Zero LITERAL Wilson Haar quadratic energy is stable under the
nonlinear full physical joint-L² Markov truncation, with no cutoff. -/
theorem p4Q2CN_originalFullJointQuadratic_truncate_zero
    (M : ℝ) (hM : 0 ≤ M) (x : J)
    (hzero : Q x = 0) :
    Q (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x) = 0 := by
  have hnonneg :=
    p4Q2BX_originalFullJointQuadratic_nonneg
      H N hN beta hbeta
      (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x)
  have hupper :=
    p4Q2CN_originalFullJointQuadratic_truncate_le
      H N hN beta hbeta M hM x
  rw [hzero] at hupper
  exact le_antisymm hupper hnonneg

/-- Consequently the KERNEL of the original physical Wilson Riesz
operator is stable under its full-L² Markov truncation. This does not
assert that the kernel has no additional unbounded elements. -/
theorem p4Q2CN_originalRieszKernel_stable_under_truncation
    (M : ℝ) (hM : 0 ≤ M) (x : J) (hx : W x = 0) :
    W (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x) = 0 := by
  have hzero : Q x = 0 :=
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta x).2 hx
  have hclip :
      Q (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x) = 0 :=
    p4Q2CN_originalFullJointQuadratic_truncate_zero
      H N hN beta hbeta M hM x hzero
  exact
    (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
      H N hN beta hbeta
      (p4Q2CN_truncatePhysicalL2 H N hN beta hbeta M hM x)).1 hclip

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
