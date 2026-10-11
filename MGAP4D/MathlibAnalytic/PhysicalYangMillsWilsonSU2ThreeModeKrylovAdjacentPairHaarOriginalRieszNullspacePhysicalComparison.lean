import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointL2RieszOperator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveColorBilinearCarrier
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-BZ: kernel of the literal Wilson Haar reference and physical E12 comparison

BX and BY construct the LITERAL original mass-weighted Wilson twelve-color
Haar reference as a positive symmetric bounded quadratic form and genuine
positive self-adjoint Riesz operator on the ACTUAL physical joint L².

This module proves the algebraic zero-diagonal annihilation lemma for a
nonnegative symmetric continuous real bilinear form; consequently the EXACT
zero-reference-energy locus equals the actual Riesz operator kernel.

Connect the prior BD/BG one-sided genuine Wilson reference comparison with
physical twelve-color conditional-expectation residual E12 on the bounded
concrete core; promote it to ALL genuine physical joint L² via the existing
dense core (BW), joint continuity and the actual E12 finite-color formula.

Thus E12(f)=0 implies the original Riesz operator annihilates f; in
particular, the intrinsic Wilson joint constant line lies IN the Riesz
operator kernel. NO reverse inequality or equality of the two kernels is
asserted. No continuum or thermodynamic Yang--Mills mass gap is asserted.
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

/-- A nonnegative symmetric REAL continuous bilinear form annihilates
a vector in one input slot when its diagonal on that vector is zero.
This does not use a spectral theorem or assume a positive gap.

The contradiction uses a concrete positive quadratic variation
(q(y)+1) x - B(x,y) y, avoiding any division by B(x,y). -/
private theorem p4Q2BZ_symmetricPositiveBilin_zeroDiagonal_annihilates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ u v : E, b u v = b v u)
    (hnonneg : ∀ u : E, 0 ≤ b u u)
    (x : E) (hx : b x x = 0) (y : E) :
    b x y = 0 := by
  let c : ℝ := b x y
  let q : ℝ := b y y
  let z : E := (q + 1) • x - c • y
  have hz : 0 ≤ b z z := hnonneg z
  have hquad : b z z = -(c ^ 2 * (q + 2)) := by
    dsimp [z]
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hx, hsymm y x]
    dsimp [c, q]
    ring
  by_contra hne
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hne
  have hq0 : 0 ≤ q := hnonneg y
  have hq2 : 0 < q + 2 := by linarith
  have hp : 0 < c ^ 2 * (q + 2) := mul_pos hc2 hq2
  rw [hquad] at hz
  linarith

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" => LinearMap.range T
local notation "BW" =>
  p4Q2BW_originalFullJointContinuousBilin H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta
local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "V" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta

/-- Pinned-mathlib operator positivity, not merely a numerical diagonal bound. -/
theorem p4Q2BZ_originalRiesz_isPositive : A.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' A).2
  exact ⟨p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta,
    p4Q2BY_originalFullJointRieszOperator_inner_nonneg H N hN beta hbeta⟩

/-- Exact radical identity: zero literal Wilson Haar reference energy
iff the genuine physical Riesz endomorphism sends the vector to zero. -/
theorem p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero (x : J) :
    Q x = 0 ↔ A x = 0 := by
  constructor
  · intro hx
    have hdiag : BW x x = 0 := hx
    have hkill : ∀ y : J, BW x y = 0 :=
      p4Q2BZ_symmetricPositiveBilin_zeroDiagonal_annihilates
        BW
        (p4Q2BX_originalFullJointBilin_symm H N hN beta hbeta)
        (p4Q2BX_originalFullJointQuadratic_nonneg H N hN beta hbeta)
        x hdiag
    apply ext_inner_right ℝ
    intro y
    rw [p4Q2BY_originalFullJointRieszOperator_inner]
    simp only [hkill y, inner_zero_left]
  · intro hx
    rw [← p4Q2BY_originalFullJointRieszOperator_quadratic]
    rw [hx, inner_zero_left]

/-- The original Wilson zero-reference-energy SET equals the exact
kernel submodule of the constructed physical Riesz operator. -/
theorem p4Q2BZ_originalZeroEnergySet_eq_Riesz_ker :
    {x : J | Q x = 0} = (A : J →ₗ[ℝ] J).ker := by
  ext x
  change Q x = 0 ↔ A x = 0
  exact p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero H N hN beta hbeta x

/-- The genuine physical 12-color conditional-expectation reference
energy is continuous in the original physical joint Hilbert L² norm. -/
theorem p4Q2BZ_physicalTwelveSpatialResidualEnergy_continuous :
    Continuous (E12 : J → ℝ) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    groundStateJointColorNormalizedResidualEnergy
  fun_prop

/-- The ORIGINAL mass-weighted Wilson twelve-color Haar reference,
already extended in BW, has the one-sided comparison to the genuine
physical conditional-expectation E12 on ALL bounded concrete L² vectors. -/
theorem p4Q2BZ_originalQuadratic_le_physicalEnergy_on_range
    (x : Img) :
    Q (x : J) ≤ (12 : ℝ) * E12 (x : J) := by
  let F : Core := p4Q2BV_originalCoreRepresentative H N hN beta hbeta x
  obtain ⟨hF, ⟨bound, hbound⟩⟩ := F.property
  have h := p4Q2BD_originalWilsonTwelveColorHaarReferenceReal_le_realEnergy
    H N hN beta hbeta F.1 hF bound hbound
  have hLift :
      p4Q2AZ_originalJointL2 H N hN beta hbeta F.1 hF bound hbound =
        (x : J) := by
    calc
      p4Q2AZ_originalJointL2 H N hN beta hbeta F.1 hF bound hbound =
          p4Q2BR_originalCorePhysicalL2 H N hN beta hbeta F :=
        (p4Q2BR_originalCorePhysicalL2_eq_originalAZ
          H N hN beta hbeta F hF bound hbound).symm
      _ = (x : J) :=
        p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta x
  rw [hLift] at h
  simpa only [p4Q2BX_originalFullJointQuadratic_on_range,
    p4Q2BP_originalCoreReference] using h

/-- All-physical-joint-L² ONE-DIRECTION Wilson comparison.
No reverse reference Poincare inequality is claimed. -/
theorem p4Q2BZ_originalQuadratic_le_twelve_physicalEnergy
    (x : J) :
    Q x ≤ (12 : ℝ) * E12 x := by
  let i : Img →L[ℝ] J := (LinearMap.range T).subtypeL
  have hd : DenseRange i :=
    p4Q2BW_originalRange_subtype_dense H N hN beta hbeta
  refine hd.induction_on x
    (isClosed_le
      (p4Q2BX_originalFullJointQuadratic_continuous H N hN beta hbeta)
      (continuous_const.mul
        (p4Q2BZ_physicalTwelveSpatialResidualEnergy_continuous
          H N hN beta hbeta))) ?_
  intro y
  exact p4Q2BZ_originalQuadratic_le_physicalEnergy_on_range
    H N hN beta hbeta y

/-- The intrinsic kernel of the physical twelve-color residual is also
annihilated by the ORIGINAL Wilson reference operator. -/
theorem p4Q2BZ_physicalEnergy_eq_zero_implies_Riesz_eq_zero
    (x : J) (hx : E12 x = 0) :
    A x = 0 := by
  have hq0 : 0 ≤ Q x :=
    p4Q2BX_originalFullJointQuadratic_nonneg H N hN beta hbeta x
  have hbound := p4Q2BZ_originalQuadratic_le_twelve_physicalEnergy
    H N hN beta hbeta x
  rw [hx] at hbound
  have hzero : Q x = 0 := by nlinarith
  exact (p4Q2BZ_originalQuadratic_eq_zero_iff_Riesz_eq_zero
    H N hN beta hbeta x).mp hzero

/-- The physical joint constant line is contained in the LITERAL Wilson
Haar reference Riesz kernel. Kernel equality is NOT claimed. -/
theorem p4Q2BZ_jointConstantLine_le_originalRiesz_ker :
    V ≤ (A : J →ₗ[ℝ] J).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply p4Q2BZ_physicalEnergy_eq_zero_implies_Riesz_eq_zero
    H N hN beta hbeta x
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta x).2 hx

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
