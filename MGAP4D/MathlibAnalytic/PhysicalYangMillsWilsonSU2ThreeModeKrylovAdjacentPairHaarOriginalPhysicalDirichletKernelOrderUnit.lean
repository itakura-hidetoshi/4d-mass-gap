import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletLoewner
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-CB: true physical twelve-color Gram kernel and Loewner unit bound

CA constructed the ACTUAL physical Wilson ground-state joint-L² twelve-color
Dirichlet Gram operator
  D12 = (card C12)⁻¹ Σ_c (id-P_c)†(id-P_c)
and the one-sided original Haar-reference Loewner domination
  0 ≤ Aoriginal ≤ 12 • D12.

This unit identifies ker D12 EXACTLY with the already established intrinsic
physical joint constant line, using the actual full-L² twelve-color
residual-energy kernel theorem and exact concrete Gram realization. It proves
the physical operator is an order contraction 0 ≤ D12 ≤ id and therefore
ker D12 ≤ ker Aoriginal. No reverse comparison or equality ker Aoriginal=V
is silently inserted.

No new physical law, no Dobrushin assumption, and no continuum mass-gap claim.
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
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "R12" =>
  p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "D" =>
  p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta

/-- Exactly the intrinsic Wilson physical joint constant submodule is the
kernel of the real physical twelve-color Dirichlet Gram endomorphism. -/
theorem p4Q2CB_physicalTwelveDirichletOperator_ker_eq_jointConstantLine :
    (D : J →ₗ[ℝ] J).ker = V := by
  ext x
  constructor
  · intro hx
    have hxD : D x = 0 := LinearMap.mem_ker.mp hx
    have hE : E12 x = 0 := by
      calc
        E12 x = inner ℝ (D x) x :=
          (p4Q2CA_physicalTwelveDirichletOperator_self H N hN beta hbeta x).symm
        _ = 0 := by rw [hxD]; exact inner_zero_left x
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
        H N hN beta hbeta x).1 hE
  · intro hV
    apply LinearMap.mem_ker.mpr
    have hE : E12 x = 0 :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
        H N hN beta hbeta x).2 hV
    have hfixed : ∀ c : C12, P12 c x = x := by
      apply (groundStateJointColorNormalizedResidualEnergy_eq_zero_iff_fixed P12 x).1
      exact hE
    have hR (c : C12) : R12 c x = 0 := by
      rw [p4Q2BG_physicalTwelveResidualOperator_apply, hfixed c]
      exact sub_self x
    unfold p4Q2CA_physicalTwelveDirichletOperator
    simp [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, hR]

/-- Physical twelve-color Gram kernel is included in the original Wilson
Haar-reference Riesz kernel. Equality of these kernels is NOT claimed. -/
theorem p4Q2CB_physicalDirichlet_ker_le_originalWilsonRiesz_ker :
    (D : J →ₗ[ℝ] J).ker ≤ (A : J →ₗ[ℝ] J).ker := by
  rw [p4Q2CB_physicalTwelveDirichletOperator_ker_eq_jointConstantLine]
  exact p4Q2BZ_jointConstantLine_le_originalRiesz_ker H N hN beta hbeta

/-- The ACTUAL physical twelve-color Gram operator is order-bounded above
by the Hilbert identity: this is BE's previously verified E12(f)≤‖f‖²
promoted to the order on continuous self-adjoint operators. -/
theorem p4Q2CB_physicalTwelveDirichletOperator_le_id :
    D ≤ ContinuousLinearMap.id ℝ J := by
  let d : J →L[ℝ] J :=
    p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
  change ((ContinuousLinearMap.id ℝ J) - d).IsPositive
  refine (ContinuousLinearMap.isPositive_iff
    ((ContinuousLinearMap.id ℝ J) - d)).2 ⟨?_, ?_⟩
  · have hd : (d : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint H N hN beta hbeta)
    change ((LinearMap.id : J →ₗ[ℝ] J) - (d : J →ₗ[ℝ] J)).IsSymmetric
    exact LinearMap.IsSymmetric.id.sub hd
  · intro x
    change 0 ≤ inner ℝ (((ContinuousLinearMap.id ℝ J) - d) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, real_inner_self_eq_norm_sq]
    change 0 ≤ ‖x‖ ^ 2 - inner ℝ (D x) x
    rw [p4Q2CA_physicalTwelveDirichletOperator_self]
    exact sub_nonneg.mpr
      (p4Q2BE_physicalTwelveResidualEnergy_le_jointNormSq H N hN beta hbeta x)

/-- Both bounds in the true physical Hilbert Loewner order: the physical
Dirichlet operator is a positive contraction in order. -/
theorem p4Q2CB_physicalTwelveDirichletOperator_Loewner_unit_interval :
    0 ≤ D ∧ D ≤ ContinuousLinearMap.id ℝ J := by
  constructor
  · exact (ContinuousLinearMap.nonneg_iff_isPositive
      (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta)).2
        (p4Q2CA_physicalTwelveDirichletOperator_isPositive H N hN beta hbeta)
  · exact p4Q2CB_physicalTwelveDirichletOperator_le_id H N hN beta hbeta

/-- The verified ordered chain of ORIGINAL Wilson Haar reference and TRUE
physical twelve-color Dirichlet operators, retaining one-sided comparison. -/
theorem p4Q2CB_originalWilson_and_physicalDirichlet_Loewner_chain :
    0 ≤ A ∧ A ≤ (12 : ℝ) • D ∧
      0 ≤ D ∧ D ≤ ContinuousLinearMap.id ℝ J := by
  rcases p4Q2CA_originalWilsonRiesz_Loewner_interval H N hN beta hbeta with
    ⟨hA0, hAD⟩
  rcases p4Q2CB_physicalTwelveDirichletOperator_Loewner_unit_interval
    H N hN beta hbeta with ⟨hD0, hDI⟩
  exact ⟨hA0, hAD, hD0, hDI⟩

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
