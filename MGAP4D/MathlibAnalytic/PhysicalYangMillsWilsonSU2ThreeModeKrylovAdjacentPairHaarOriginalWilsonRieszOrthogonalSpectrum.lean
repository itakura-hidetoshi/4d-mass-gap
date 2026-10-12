import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointHaarRieszCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletOrthogonalSpectrum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullL2QualitativeKernelCollapse
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

/-!
# P4-Q2-DW: original Wilson Haar Riesz operator Loewner and spectral gap

DV gives a positive finite-volume quadratic coercivity coefficient for the
LITERAL original Wilson Haar-reference continuous Riesz quadratic on the
ENTIRE original physical Wilson ground-state joint real L².

This file transfers that SAME inequality to the ACTUAL BY Riesz operator,
not the distinct physical conditional-expectation D12. It proves a genuine
positive Loewner comparison with the centered Wilson constant projection,
annihilation and preservation of the genuine Wilson constant-orthogonal
sector, its continuous self-adjoint restriction, and a positive REAL Banach
spectrum floor using the pinned mathlib coercive isUnit theorem.

Independently, BF's established upper E12 ≤ ‖x - Pconst x‖² upgrades the
same DV coefficient to the bilateral finite-volume Loewner comparison
    κ D12 ≤ Aoriginal ≤ 12 D12.
No Wilson/pair-Haar projection or mean identification is introduced.

The coefficient may depend on finite H, N, and beta. These results do NOT
assert a volume/spacing-uniform bound, adjacent-scale reconstruction, an
Osterwalder--Schrader continuum Hamiltonian, or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace NNReal

noncomputable section

set_option maxHeartbeats 2600000
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
local notation "A" =>
  p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
local notation "Q" =>
  p4Q2BX_originalFullJointQuadratic H N hN beta hbeta
local notation "D12" =>
  p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

local instance p4Q2DW_constantLineHasOrthogonalProjection :
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

/-- Genuine original Wilson Riesz Loewner lower bound on ALL physical L²,
with the centered residual (id - physical Wilson Pconstant). -/
theorem p4Q2DW_originalWilsonRiesz_ge_centeredResidual :
    ∃ κ : ℝ, 0 < κ ∧
      κ • p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta ≤ A := by
  obtain ⟨κ, hκ, hDV⟩ :=
    p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  let W : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  let R : J →L[ℝ] J :=
    p4Q2DT_physicalCenteredResidualOperator H N hN beta hbeta
  change (W - κ • R).IsPositive
  refine (ContinuousLinearMap.isPositive_iff (W - κ • R)).2 ⟨?_, ?_⟩
  · have hw : (W : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
    have hr : (R : J →ₗ[ℝ] J).IsSymmetric :=
      p4Q2DT_physicalCenteredResidualOperator_symmetric H N hN beta hbeta
    change ((W : J →ₗ[ℝ] J) - κ • (R : J →ₗ[ℝ] J)).IsSymmetric
    exact hw.sub (hr.smul (by simp))
  · intro x
    change 0 ≤ inner ℝ ((W - κ • R) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    have hW : inner ℝ (W x) x = Q x :=
      p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta x
    have hR : inner ℝ (R x) x = ‖x - B x‖ ^ 2 :=
      p4Q2DT_physicalCenteredResidualOperator_inner_self H N hN beta hbeta x
    rw [hW, hR]
    exact sub_nonneg.mpr (hDV x)

/-- Original Wilson Haar Riesz annihilates physical Wilson constants,
using the existing CC/CO kernel chain (no new kernel assertion). -/
theorem p4Q2DW_originalWilsonRiesz_zero_of_mem_constantLine
    (x : J) (hx : x ∈ V) : A x = 0 :=
  p4Q2CC_originalWilsonRiesz_zero_of_mem_constantLine H N hN beta hbeta x hx

/-- Self-adjointness and exact constant-line annihilation imply that
every original Wilson Riesz output lies in the physical V-orthogonal space. -/
theorem p4Q2DW_originalWilsonRiesz_mem_orthogonal
    (x : J) : A x ∈ Vᗮ := by
  have hsym :
      ∀ u v : J, inner ℝ (A u) v = inner ℝ u (A v) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
      (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
  apply (Submodule.mem_orthogonal
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta) (A x)).2
  intro y hy
  calc
    inner ℝ y (A x) = inner ℝ (A y) x := (hsym y x).symm
    _ = 0 := by
      rw [p4Q2DW_originalWilsonRiesz_zero_of_mem_constantLine
        H N hN beta hbeta y hy]
      simp

/-- Actual bounded restriction of the ORIGINAL Riesz operator to the
original physical Wilson constant-line orthogonal Hilbert subspace. -/
noncomputable def p4Q2DW_restrictedOriginalWilsonRiesz :
    (Vᗮ) →L[ℝ] (Vᗮ) := by
  let W : Submodule ℝ J :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta)ᗮ
  let T : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  exact (T.comp W.subtypeL).codRestrict W
    (fun x => p4Q2DW_originalWilsonRiesz_mem_orthogonal
      H N hN beta hbeta (x : J))

@[simp] theorem p4Q2DW_restrictedOriginalWilsonRiesz_apply
    (x : Vᗮ) :
    ((p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta x : Vᗮ) : J) =
      A (x : J) := by
  rfl

/-- Restricted operator retains EXACT original continuous Haar-reference
quadratic (not the conditional-expectation physical Dirichlet form). -/
theorem p4Q2DW_restrictedOriginalWilsonRiesz_inner_self
    (x : Vᗮ) :
    inner ℝ (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta x) x =
      Q (x : J) := by
  change inner ℝ (A (x : J)) (x : J) = Q (x : J)
  exact p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta (x : J)

/-- Self-adjointness of the ORIGINAL bounded Wilson Riesz restriction. -/
theorem p4Q2DW_restrictedOriginalWilsonRiesz_isSelfAdjoint :
    IsSelfAdjoint (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2
  intro x y
  change inner ℝ (A (x : J)) (y : J) =
    inner ℝ (x : J) (A (y : J))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
    (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
      (x : J) (y : J)

/-- Strictly positive finite-volume original Wilson Riesz Rayleigh
constant on the ACTUAL Wilson-constant orthogonal sector. -/
theorem p4Q2DW_restrictedOriginalWilsonRiesz_positiveRayleigh :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : Vᗮ,
        κ * ‖x‖ ^ 2 ≤
          inner ℝ (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta x) x := by
  obtain ⟨κ, hκ, hDV⟩ :=
    p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro x
  have hB : B (x : J) = 0 := by
    let W :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change W.starProjection (x : J) = 0
    exact (W.starProjection_apply_eq_zero_iff).2 x.property
  have hx := hDV (x : J)
  rw [hB, sub_zero] at hx
  change κ * ‖(x : J)‖ ^ 2 ≤ inner ℝ (A (x : J)) (x : J)
  rw [p4Q2BY_originalFullJointRieszOperator_quadratic]
  exact hx

/-- Actual REAL Banach algebra spectrum of the ORIGINAL Wilson Haar Riesz
operator, restricted to physical Wilson Vᗮ, lies above a positive finite-
volume coefficient. Invertibility for EVERY real t < κ is explicit. -/
theorem p4Q2DW_restrictedOriginalWilsonRiesz_spectrum_subset_Ici :
    ∃ κ : ℝ, 0 < κ ∧
      spectrum ℝ (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta) ⊆
        Set.Ici κ := by
  let W : Submodule ℝ J :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta)ᗮ
  let T : W →L[ℝ] W :=
    p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta
  obtain ⟨κ, hκ, hRay⟩ :=
    p4Q2DW_restrictedOriginalWilsonRiesz_positiveRayleigh H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro t ht
  change κ ≤ t
  by_contra hnot
  have hlt : t < κ := lt_of_not_ge hnot
  let c : ℝ≥0 := ⟨κ - t, le_of_lt (sub_pos.mpr hlt)⟩
  have hc : 0 < c := by
    change (0 : ℝ) < κ - t
    exact sub_pos.mpr hlt
  have hunit : IsUnit ((algebraMap ℝ (W →L[ℝ] W)) t - T) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      ((algebraMap ℝ (W →L[ℝ] W)) t - T) hc
    intro x
    have hbound : κ * ‖x‖ ^ 2 ≤ inner ℝ (T x) x := hRay x
    have hshift :
        inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) t - T) x) x =
          t * ‖x‖ ^ 2 - inner ℝ (T x) x := by
      simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, real_inner_smul_left]
    have hnegative :
        ‖x‖ ^ 2 * (c : ℝ) ≤
          -(inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) t - T) x) x) := by
      rw [hshift]
      change ‖x‖ ^ 2 * (κ - t) ≤
        -(t * ‖x‖ ^ 2 - inner ℝ (T x) x)
      nlinarith [hbound]
    exact hnegative.trans (by
      rw [Real.norm_eq_abs]
      exact neg_le_abs _)
  have hnotmem :
      t ∉ spectrum ℝ (p4Q2DW_restrictedOriginalWilsonRiesz H N hN beta hbeta) := by
    exact (spectrum.notMem_iff).2 hunit
  exact (hnotmem ht).elim

/-- Additional finite-volume reverse comparison: BF's actual physical
normalized D12 energy is bounded by centered squared norm; DV controls
the latter by the ORIGINAL Wilson Haar Riesz quadratic. -/
theorem p4Q2DW_originalWilsonRiesz_ge_physicalD12 :
    ∃ κ : ℝ, 0 < κ ∧ κ • D12 ≤ A := by
  obtain ⟨κ, hκ, hDV⟩ :=
    p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive
      H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  let W : J →L[ℝ] J :=
    p4Q2BY_originalFullJointRieszOperator H N hN beta hbeta
  let D : J →L[ℝ] J :=
    p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
  change (W - κ • D).IsPositive
  refine (ContinuousLinearMap.isPositive_iff (W - κ • D)).2 ⟨?_, ?_⟩
  · have hw : (W : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2BY_originalFullJointRieszOperator_isSelfAdjoint H N hN beta hbeta)
    have hd : (D : J →ₗ[ℝ] J).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
        (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint H N hN beta hbeta)
    change ((W : J →ₗ[ℝ] J) - κ • (D : J →ₗ[ℝ] J)).IsSymmetric
    exact hw.sub (hd.smul (by simp))
  · intro x
    change 0 ≤ inner ℝ ((W - κ • D) x) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, real_inner_smul_left]
    have hW : inner ℝ (W x) x = Q x :=
      p4Q2BY_originalFullJointRieszOperator_quadratic H N hN beta hbeta x
    have hD : inner ℝ (D x) x = E12 x :=
      p4Q2CA_physicalTwelveDirichletOperator_self H N hN beta hbeta x
    rw [hW, hD]
    have hEnergy : E12 x ≤ ‖x - B x‖ ^ 2 :=
      p4Q2BF_physicalTwelveResidualEnergy_le_centeredJointNormSq
        H N hN beta hbeta x
    have hScale : κ * E12 x ≤ κ * ‖x - B x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hEnergy hκ.le
    exact sub_nonneg.mpr (hScale.trans (hDV x))

/-- Both directions of the finite-volume operator comparison on the SAME
physical joint Wilson L²; original A and distinct normalized physical D12
are NOT identified. -/
theorem p4Q2DW_originalWilsonRiesz_physicalD12_bilateral :
    ∃ κ : ℝ, 0 < κ ∧
      κ • D12 ≤ A ∧ A ≤ (12 : ℝ) • D12 := by
  obtain ⟨κ, hκ, hlower⟩ :=
    p4Q2DW_originalWilsonRiesz_ge_physicalD12 H N hN beta hbeta
  exact ⟨κ, hκ, hlower,
    p4Q2CA_originalWilsonRiesz_le_twelve_physicalDirichlet
      H N hN beta hbeta⟩

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2DW_originalWilsonRiesz_ge_centeredResidual
#print axioms MGAP4D.MathlibAnalytic.p4Q2DW_restrictedOriginalWilsonRiesz_spectrum_subset_Ici
#print axioms MGAP4D.MathlibAnalytic.p4Q2DW_originalWilsonRiesz_physicalD12_bilateral
