import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonFullJointL2PhysicalFrameCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletLoewner
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-DT: genuine positive finite-volume Wilson physical D12 operator gap

DS proves one positive coefficient on the ENTIRE genuine original physical
Wilson joint real L² Hilbert space, coercing the squared norm orthogonal
to the actual Wilson constant line by the original two-boundary twelve-color
conditional expectation Dirichlet energy E12.

CA already constructs the corresponding self-adjoint positive bounded
continuous real linear endomorphism D12 of the SAME physical Hilbert space
as an exact finite sum of genuine residual Gram operators and proves
  inner ℝ (D12 x) x = E12 x.

This file proves the exact self-adjoint Loewner operator bound
  0 < κ(H,N,beta),   κ • (id - P_const) ≤ D12
on the physical joint L², including the variational lower Rayleigh bound
on the orthogonal complement of ACTUAL constant Wilson observables.

The proof uses the pinned mathlib orthogonal starProjection identities,
not an assumed commuting family of interacting Wilson conditionals.
All coefficients may depend on finite volume H, N and beta. NO gap for the
distinct original Wilson Haar Riesz operator, no volume/spacing-uniform gap,
and no continuum 4D Yang--Mills mass-gap assertion is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

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

local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta
local notation "D12" =>
  p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

local instance p4Q2DT_constantLineHasOrthogonalProjection :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change W.HasOrthogonalProjection
  letI : FiniteDimensional ℝ W := by
    unfold W
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace W

/-- The actual physical constant-orthogonal residual is a bounded linear
operator on the SAME physical Wilson joint L², not a synthetic quotient. -/
noncomputable def p4Q2DT_physicalCenteredResidualOperator : J →L[ℝ] J :=
  ContinuousLinearMap.id ℝ J - B

@[simp] theorem p4Q2DT_physicalCenteredResidualOperator_apply (x : J) :
    p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta x = x - B x := by
  simp [p4Q2DT_physicalCenteredResidualOperator]

/-- Actual physical star-projection orthogonality gives an exact REAL
Hilbert quadratic identity for the complementary projection id - B. -/
theorem p4Q2DT_physicalCenteredResidualOperator_inner_self
    (x : J) :
    inner ℝ (p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta x) x =
      ‖x - B x‖ ^ 2 := by
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  have hz : inner ℝ (x - W.starProjection x) (W.starProjection x) = 0 :=
    W.starProjection_inner_eq_zero x _ (W.starProjection_apply_mem x)
  change inner ℝ (x - W.starProjection x) x = ‖x - W.starProjection x‖ ^ 2
  have hx : x = (x - W.starProjection x) + W.starProjection x := by abel
  calc
    inner ℝ (x - W.starProjection x) x =
        inner ℝ (x - W.starProjection x)
          ((x - W.starProjection x) + W.starProjection x) := by
            rw [← hx]
    _ = inner ℝ (x - W.starProjection x) (x - W.starProjection x) +
          inner ℝ (x - W.starProjection x) (W.starProjection x) := inner_add_right _ _ _
    _ = inner ℝ (x - W.starProjection x) (x - W.starProjection x) := by
          rw [hz, add_zero]
    _ = ‖x - W.starProjection x‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- The actual physical centered residual operator is symmetric, by
the self-adjointness of the genuine Wilson constant-line starProjection. -/
theorem p4Q2DT_physicalCenteredResidualOperator_symmetric :
    (p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta :
      J →ₗ[ℝ] J).IsSymmetric := by
  intro x y
  change inner ℝ (x - B x) y = inner ℝ x (y - B y)
  rw [inner_sub_left, inner_sub_right]
  congr 1
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change inner ℝ (W.starProjection x) y = inner ℝ x (W.starProjection y)
  exact W.inner_starProjection_left_eq_right x y

/-- GENUINE OPERATOR LOEWNER LOWER BOUND on the entire physical Wilson L²:
the positive finite-volume coefficient multiplies the actual orthogonal
complement projection, not the unrelated original Haar-reference Riesz map. -/
theorem p4Q2DT_physicalTwelveDirichlet_ge_centeredResidualOperator :
    ∃ κ : ℝ, 0 < κ ∧
      κ • p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta ≤ D12 := by
  obtain ⟨κ, hκ, hDS⟩ :=
    p4Q2DS_originalWilsonFullJointL2_physicalTwelveColor_coercive
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  let D : J →L[ℝ] J := D12
  let R : J →L[ℝ] J :=
    p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta
  change (D - κ • R).IsPositive
  refine (ContinuousLinearMap.isPositive_iff (D - κ • R)).2 ⟨?_, ?_⟩
  · have hd : (D : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint
          H N hN beta hbeta)
    have hr : (R : J →ₗ[ℝ] J).IsSymmetric :=
      p4Q2DT_physicalCenteredResidualOperator_symmetric H N hN beta hbeta
    change ((D : J →ₗ[ℝ] J) - κ • (R : J →ₗ[ℝ] J)).IsSymmetric
    exact hd.sub (hr.smul (by simp))
  · intro x
    change 0 ≤ inner ℝ ((D - κ • R) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    have hD : inner ℝ (D x) x = E12 x :=
      p4Q2CA_physicalTwelveDirichletOperator_self H N hN beta hbeta x
    have hR : inner ℝ (R x) x = ‖x - B x‖ ^ 2 :=
      p4Q2DT_physicalCenteredResidualOperator_inner_self H N hN beta hbeta x
    rw [hD, hR]
    exact sub_nonneg.mpr (hDS x)

/-- The SAME positive coefficient bounds the physical self-adjoint D12
Rayleigh quotient on each ACTUAL constant-orthogonal physical vector. -/
theorem p4Q2DT_physicalTwelveDirichlet_orthogonalRayleigh :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : J, x ∈ Vᗮ →
        κ * ‖x‖ ^ 2 ≤ inner ℝ (D12 x) x := by
  obtain ⟨κ, hκ, hDS⟩ :=
    p4Q2DS_originalWilsonFullJointL2_physicalTwelveColor_coercive
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro x hx
  have hB : B x = 0 := by
    let W :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change W.starProjection x = 0
    exact (W.starProjection_apply_eq_zero_iff).2 hx
  have h := hDS x
  rw [hB, sub_zero] at h
  rw [p4Q2CA_physicalTwelveDirichletOperator_self H N hN beta hbeta]
  exact h

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
