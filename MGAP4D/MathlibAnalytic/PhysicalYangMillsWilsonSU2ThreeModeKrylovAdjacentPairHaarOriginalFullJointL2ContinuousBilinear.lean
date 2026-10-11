import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRangeContinuousBilinear
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteCoreDensity
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-!
# P4-Q2-BW: original Wilson twelve-color reference on the whole physical joint L²

The bounded strongly measurable concrete Wilson core has dense image in the
ACTUAL physical ground-state joint L² (the existing bounded-core density theorem).
BV gives the genuine original mass-weighted Haar-reference continuous real
bilinear form with operator bound 12 on that image. We extend it along the
isometric dense submodule inclusion, first in one variable and then in the
other, using pinned mathlib's `ContinuousLinearMap.extend` and `flip`.

We prove exact agreement on the original image, the same norm-12 estimate and
uniqueness among continuous bilinear extensions. The diagonal therefore retains
the literal original twelve-color Wilson Haar reference on bounded observables.

This is a finite-volume Hilbert-space extension. It is not a reverse
Haar/Poincare comparison, infinite-volume limit, continuum limit, or mass gap.
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
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "B" =>
  p4Q2BV_originalRangeContinuousBilin H N hN beta hbeta

/-- The existing physically defined bounded concrete L² core lies in the
range of the actual BR linear quotient map, not just in an abstract completion.
The equality is proved in the genuine L² quotient using the a.e. representatives. -/
theorem p4Q2BW_boundedConcreteCore_subset_originalRange :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta ⊆ (Img : Set J) := by
  intro f hf
  rcases hf with ⟨F, hF, bound, hbound, hf⟩
  let c : Core := ⟨F, ⟨hF, ⟨bound, hbound⟩⟩⟩
  apply LinearMap.mem_range.mpr
  refine ⟨c, ?_⟩
  change p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta c = f
  rw [← hf]
  apply Lp.ext
  exact
    (MemLp.coeFn_toLp (p4Q2BR_originalCore_memLp H N hN beta hbeta c)).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
        H N hN beta hbeta F hF bound hbound).symm

/-- The ACTUAL Wilson bounded-core image is dense in the entire original
physical ground-state joint L², by the already merged simple-function theorem. -/
theorem p4Q2BW_originalRange_dense : Dense (Img : Set J) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
    H N hN beta hbeta).mono
      (p4Q2BW_boundedConcreteCore_subset_originalRange H N hN beta hbeta)

/-- Dense range of the genuine norm-preserving submodule inclusion. -/
theorem p4Q2BW_originalRange_subtype_dense :
    DenseRange ((LinearMap.range T).subtypeL : Img →L[ℝ] J) := by
  have hd := p4Q2BW_originalRange_dense H N hN beta hbeta
  change Dense (Set.range (fun x : Img => (x : J)))
  have heq : (Set.range (fun x : Img => (x : J))) = (Img : Set J) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [heq]
  exact hd

/-- Extend BV's genuine continuous Wilson bilinear operator in the first
variable, with complete codomain given by bounded functionals on the core. -/
noncomputable def p4Q2BW_originalFirstExtended :
    J →L[ℝ] Img →L[ℝ] ℝ :=
  (p4Q2BV_originalRangeContinuousBilin H N hN beta hbeta).extend
    ((LinearMap.range T).subtypeL : Img →L[ℝ] J)

/-- Extend also in the second variable, then flip back to the standard order.
This is an ACTUAL bounded real bilinear map on the entire original physical
Wilson joint L², not merely an algebraic map on a dense core. -/
noncomputable def p4Q2BW_originalFullJointContinuousBilin :
    J →L[ℝ] J →L[ℝ] ℝ :=
  ((p4Q2BW_originalFirstExtended H N hN beta hbeta).flip.extend
    ((LinearMap.range T).subtypeL : Img →L[ℝ] J)).flip

/-- Exact recovery of the BV form on every bounded physical core image pair. -/
theorem p4Q2BW_originalFullJointContinuousBilin_apply_range
    (x y : Img) :
    p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
        (x : J) (y : J) =
      B x y := by
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  let b := B
  let b₁ := p4Q2BW_originalFirstExtended H N hN beta hbeta
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  have hi : IsUniformInducing (i : Img → J) := by
    change IsUniformInducing (Subtype.val : Img → J)
    exact isUniformEmbedding_subtype_val.isUniformInducing
  calc
    p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
        (x : J) (y : J) =
        (b₁.flip.extend i) (i y) (i x) := rfl
    _ = b₁.flip y (i x) :=
      ContinuousLinearMap.extend_eq b₁.flip hd hi y
    _ = b₁ (i x) y := rfl
    _ = b x y := by
      change (b.extend i) (i x) y = b x y
      rw [ContinuousLinearMap.extend_eq b hd hi x]

/-- The norm-12 coefficient in BV is the operator-norm estimate, not merely
a pointwise bound for a chosen pair of representatives. -/
theorem p4Q2BW_originalRangeBilin_opNorm_le :
    ‖B‖ ≤ (12 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound₂ B (by norm_num) ?_
  intro x y
  simpa only [p4Q2BV_originalRangeContinuousBilin_apply, mul_assoc] using
    (p4Q2BV_originalRangePolarization_norm_le H N hN beta hbeta x y)

/-- Extending in both slots along the dense isometric inclusion does not
increase the operator norm: the literal Wilson constant 12 is preserved. -/
theorem p4Q2BW_originalFullJointContinuousBilin_opNorm_le :
    ‖p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta‖ ≤
      (12 : ℝ) := by
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  let b := B
  let b₁ := p4Q2BW_originalFirstExtended H N hN beta hbeta
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  have hiNorm : ∀ x : Img, ‖x‖ ≤ (1 : ℝ≥0) * ‖i x‖ := by
    intro x
    simp
  have hfirst : ‖b₁‖ ≤ ‖b‖ := by
    simpa [b₁, b] using
      (b.opNorm_extend_le (e := i) (N := (1 : ℝ≥0)) hd hiNorm)
  have hsecond : ‖b₁.flip.extend i‖ ≤ ‖b₁.flip‖ := by
    simpa using
      (b₁.flip.opNorm_extend_le (e := i) (N := (1 : ℝ≥0)) hd hiNorm)
  calc
    ‖p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta‖ =
        ‖b₁.flip.extend i‖ := by
      change ‖(b₁.flip.extend i).flip‖ = ‖b₁.flip.extend i‖
      simp
    _ ≤ ‖b₁.flip‖ := hsecond
    _ = ‖b₁‖ := by simp
    _ ≤ ‖b‖ := hfirst
    _ ≤ (12 : ℝ) := p4Q2BW_originalRangeBilin_opNorm_le H N hN beta hbeta

/-- Uniform mixed estimate on ALL original physical Wilson joint L² classes,
not just strongly measurable bounded concrete representatives. -/
theorem p4Q2BW_originalFullJointContinuousBilin_norm_le (x y : J) :
    ‖p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta x y‖ ≤
      (12 : ℝ) * ‖x‖ * ‖y‖ := by
  calc
    ‖p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta x y‖ ≤
      ‖p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta‖ *
        ‖x‖ * ‖y‖ :=
      (p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta).le_opNorm₂ x y
    _ ≤ (12 : ℝ) * ‖x‖ * ‖y‖ := by
      gcongr
      exact p4Q2BW_originalFullJointContinuousBilin_opNorm_le
        H N hN beta hbeta

/-- The full-space diagonal agrees EXACTLY with the original
mass-weighted Wilson twelve-color Haar reference for a bounded representative. -/
theorem p4Q2BW_originalFullJointContinuousBilin_self_on_range
    (x : Img) :
    p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta (x : J) (x : J) =
      p4Q2BP_originalCoreReference H N hN beta hbeta
        (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) := by
  rw [p4Q2BW_originalFullJointContinuousBilin_apply_range]
  exact p4Q2BV_originalRangeContinuousBilin_self H N hN beta hbeta x

/-- Uniqueness of the ACTUAL continuous Hilbert-wide bilinear extension;
the dense original bounded-core image determines both slots. -/
theorem p4Q2BW_originalFullJointContinuousBilin_unique
    (other : J →L[ℝ] J →L[ℝ] ℝ)
    (hcore : ∀ x y : Img, other (x : J) (y : J) = B x y) :
    other = p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta := by
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  let full := p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
  have hpointwise : (fun z : J => other z) = (fun z : J => full z) := by
    apply hd.equalizer other.continuous full.continuous
    funext x
    apply ContinuousLinearMap.ext
    intro z
    change other (x : J) z = full (x : J) z
    have hsecond : (fun w : J => other (x : J) w) =
        (fun w : J => full (x : J) w) := by
      apply hd.equalizer (other (x : J)).continuous (full (x : J)).continuous
      funext y
      change other (x : J) (y : J) = full (x : J) (y : J)
      calc
        other (x : J) (y : J) = B x y := hcore x y
        _ = full (x : J) (y : J) :=
          (p4Q2BW_originalFullJointContinuousBilin_apply_range
            H N hN beta hbeta x y).symm
    exact congrFun hsecond z
  apply ContinuousLinearMap.ext
  intro x
  exact congrFun hpointwise x

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
