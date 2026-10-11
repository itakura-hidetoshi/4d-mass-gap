import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRieszNullspacePhysicalComparison
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# P4-Q2-CA: exact physical twelve-color Dirichlet operator and original Wilson Loewner order

The sole authoritative physical Wilson joint L² and the genuine twelve spatial
right/left conditional expectation operators are retained unchanged.

Build the finite-color positive Gram operator
  D12 = (card C12)⁻¹ Σ_c (id-P_c)† ∘ (id-P_c)
as an ACTUAL continuous real-linear endomorphism of the ORIGINAL ground-state
joint L². Its Hilbert matrix coefficients are the literal BG physical residual
pairing, and its diagonal is the old physical twelve-color E12.

Use BZ's PROVED one-sided full-L² original Wilson Haar-reference comparison
  Qoriginal(f) ≤ 12 E12(f),
together with BY's ACTUAL Riesz operator Aoriginal, to prove the genuine
mathlib Loewner order on bounded self-adjoint physical Hilbert operators:
  0 ≤ Aoriginal ≤ 12 • D12.

This does NOT reverse the original Wilson comparison or prove ker Aoriginal
= constants, an inverse reference gap, or any continuum Yang--Mills mass gap.
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
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta

/-- Exactly the genuine physical Wilson twelve-color residual Gram
operator on the existing original physical ground-state joint Hilbert L².
Every term is the adjoint-square of the actual spatial residual id - P_c. -/
noncomputable def p4Q2CA_physicalTwelveDirichletOperator : J →L[ℝ] J :=
  ((Fintype.card C12 : ℝ)⁻¹) •
    ∑ c : C12, (R12 c).adjoint ∘L (R12 c)

/-- Every physical Dirichlet Gram matrix element is EXACTLY the old BG
symmetric residual pairing; this is not the separate Wilson Haar reference. -/
theorem p4Q2CA_physicalTwelveDirichletOperator_inner (f g : J) :
    inner ℝ (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta f) g =
      p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g := by
  unfold p4Q2CA_physicalTwelveDirichletOperator
    p4Q2BG_physicalTwelveResidualPair
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    real_inner_smul_left, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro c _hc
  exact (R12 c).adjoint_inner_left g ((R12 c) f)

/-- The physical D12 Gram diagonal is definitionally the PREEXISTING
normalized twelve-color conditional-expectation Dirichlet energy. -/
theorem p4Q2CA_physicalTwelveDirichletOperator_self (f : J) :
    inner ℝ (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta f) f =
      E12 f := by
  rw [p4Q2CA_physicalTwelveDirichletOperator_inner]
  exact p4Q2BG_physicalTwelveResidualPair_self_eq_energy H N hN beta hbeta f

/-- The ACTUAL physical twelve-color Dirichlet operator is self-adjoint
on the original joint Wilson Hilbert L², without color commutativity. -/
theorem p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint :
    IsSelfAdjoint (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2
  intro f g
  change inner ℝ
    (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta f) g =
    inner ℝ f
      (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta g)
  calc
    inner ℝ (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta f) g =
        p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta f g :=
      p4Q2CA_physicalTwelveDirichletOperator_inner H N hN beta hbeta f g
    _ = p4Q2BG_physicalTwelveResidualPair H N hN beta hbeta g f :=
      p4Q2BG_physicalTwelveResidualPair_symmetric H N hN beta hbeta f g
    _ = inner ℝ
          (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta g) f :=
      (p4Q2CA_physicalTwelveDirichletOperator_inner H N hN beta hbeta g f).symm
    _ = inner ℝ f
          (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta g) :=
      real_inner_comm _ _

/-- Full physical Dirichlet operator positivity in the PINNED mathlib order. -/
theorem p4Q2CA_physicalTwelveDirichletOperator_isPositive :
    (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff'
    (p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta)).2
  constructor
  · exact p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint H N hN beta hbeta
  · intro f
    rw [p4Q2CA_physicalTwelveDirichletOperator_self]
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    exact groundStateJointColorNormalizedResidualEnergy_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta) f

/-- TRUE operator-valued Loewner comparison, obtained from the earlier
one-direction original Wilson L² quadratic bound and the two genuine
self-adjoint physical representatives.
This DOES NOT assert the reverse comparison. -/
theorem p4Q2CA_originalWilsonRiesz_le_twelve_physicalDirichlet :
    A ≤ (12 : ℝ) •
      p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta := by
  let D : J →L[ℝ] J :=
    p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
  let W : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  change ((12 : ℝ) • D - W).IsPositive
  refine (ContinuousLinearMap.isPositive_iff ((12 : ℝ) • D - W)).2 ⟨?_, ?_⟩
  · have hd : (D : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint H N hN beta hbeta)
    have hw : (W : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
    change (((12 : ℝ) • (D : J →ₗ[ℝ] J)) - (W : J →ₗ[ℝ] J)).IsSymmetric
    exact (hd.smul (by simp)).sub hw
  · intro f
    change 0 ≤ inner ℝ (((12 : ℝ) • D - W) f) f
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    change 0 ≤
      (12 : ℝ) * inner ℝ (D f) f - inner ℝ (W f) f
    rw [p4Q2CA_physicalTwelveDirichletOperator_self,
      p4Q2BY_originalFullJointRieszOperator_quadratic]
    exact sub_nonneg.mpr
      (p4Q2BZ_originalQuadratic_le_twelve_physicalEnergy H N hN beta hbeta f)

/-- The final certified Loewner interval for the ORIGINAL Wilson Haar
Riesz operator, relative to the separately defined genuine physical
twelve-color Dirichlet operator. -/
theorem p4Q2CA_originalWilsonRiesz_Loewner_interval :
    0 ≤ A ∧
      A ≤ (12 : ℝ) •
        p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta := by
  constructor
  · exact (ContinuousLinearMap.nonneg_iff_isPositive
      (p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta)).2
        (p4Q2BZ_originalRiesz_isPositive H N hN beta hbeta)
  · exact p4Q2CA_originalWilsonRiesz_le_twelve_physicalDirichlet
      H N hN beta hbeta

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
