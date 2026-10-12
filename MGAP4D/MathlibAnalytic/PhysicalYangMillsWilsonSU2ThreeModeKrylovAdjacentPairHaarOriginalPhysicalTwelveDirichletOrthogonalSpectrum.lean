import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletOperatorGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalTwelveDirichletLoewner
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

/-!
# P4-Q2-DU: genuine physical Wilson D12 restricted spectrum above zero

DT proved a positive finite-volume Loewner and Rayleigh bound for the
ACTUAL 12-color physical Wilson Dirichlet Gram operator D12 on the true
Wilson joint real L², modulo its original physical constant-line sector.

We first prove that D12 annihilates the entire genuine constant line,
using the EXISTING twelve-color conditional expectation common-fixed
characterization and CA's exact finite sum of residual Gram operators.
The existing true self-adjointness then implies D12 maps the entire
physical L² into the orthogonal complement Vᗮ.

We define the actual continuous linear restriction D12|Vᗮ and prove
that it is self-adjoint with exactly the genuine physical quadratic
energy on embedded inputs. DT gives its positive finite-volume
Rayleigh bound, and the pinned mathlib coercive invertibility lemma
excludes EVERY real λ < κ from its Banach algebra spectrum.

No compactness, discrete eigenbasis, interacting Wilson color
commutation, new physical probability law, or Wilson Haar Riesz
coercivity is assumed. The coefficient depends on H,N,beta.
This does not assert a volume/spacing-uniform 4D Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace NNReal

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
local notation "C12" =>
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor
local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta
local notation "R12" =>
  p4Q2BG_physicalTwelveResidualOperator H N hN beta hbeta
local notation "D12" =>
  p4Q2CA_physicalTwelveDirichletOperator H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

/-- Every actual Wilson-constant joint L² vector is killed by the genuine
physical D12 operator, not merely by the scalar E12 quadratic energy. -/
theorem p4Q2DU_physicalD12_zero_of_mem_constantLine
    (x : J) (hx : x ∈ V) :
    D12 x = 0 := by
  have hZero : E12 x = 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_eq_zero_iff_mem_constantLine
      H N hN beta hbeta x).2 hx
  have hFixed : ∀ c : C12, P12 c x = x :=
    (groundStateJointColorNormalizedResidualEnergy_eq_zero_iff_fixed P12 x).1 hZero
  have hResidual (c : C12) : R12 c x = 0 := by
    rw [p4Q2BG_physicalTwelveResidualOperator_apply, hFixed c, sub_self]
  change
    (((Fintype.card C12 : ℝ)⁻¹) •
      (∑ c : C12, (R12 c).adjoint ∘L (R12 c))) x = 0
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  simp [hResidual]

/-- Since the physical D12 is self-adjoint and kills genuine Wilson constants,
EVERY D12 output is Wilson-constant-orthogonal. This is stronger than
invariance of Vᗮ and does not assume any commuting color conditionals. -/
theorem p4Q2DU_physicalD12_mem_orthogonal
    (x : J) : D12 x ∈ Vᗮ := by
  have hsym :
      ∀ u v : J, inner ℝ (D12 u) v = inner ℝ u (D12 v) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
      (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint
        H N hN beta hbeta)
  apply (V.mem_orthogonal (D12 x)).2
  intro y hy
  calc
    inner ℝ y (D12 x) = inner ℝ (D12 y) x := (hsym y x).symm
    _ = 0 := by
      rw [p4Q2DU_physicalD12_zero_of_mem_constantLine H N hN beta hbeta y hy]
      simp

/-- ACTUAL original physical D12 restriction to the closed Hilbert
orthogonal complement of the physical Wilson constant line. -/
noncomputable def p4Q2DU_restrictedPhysicalD12 :
    (Vᗮ) →L[ℝ] (Vᗮ) :=
  D12.restrict (fun x _hx =>
    p4Q2DU_physicalD12_mem_orthogonal H N hN beta hbeta x)

@[simp] theorem p4Q2DU_restrictedPhysicalD12_apply
    (x : Vᗮ) :
    ((p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta x : Vᗮ) : J) =
      D12 (x : J) := by
  rfl

/-- The original physical D12 inner product is retained EXACTLY
after restriction; no new auxiliary quadratic is constructed. -/
theorem p4Q2DU_restrictedPhysicalD12_inner_self
    (x : Vᗮ) :
    inner ℝ (p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta x) x =
      E12 (x : J) := by
  change inner ℝ (D12 (x : J)) (x : J) = E12 (x : J)
  exact p4Q2CA_physicalTwelveDirichletOperator_self H N hN beta hbeta (x : J)

/-- Genuine self-adjointness of the physical D12 operator on the
closed constant-orthogonal Hilbert subspace. -/
theorem p4Q2DU_restrictedPhysicalD12_isSelfAdjoint :
    IsSelfAdjoint (p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2
  intro x y
  change inner ℝ (D12 (x : J)) (y : J) =
    inner ℝ (x : J) (D12 (y : J))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1
    (p4Q2CA_physicalTwelveDirichletOperator_isSelfAdjoint H N hN beta hbeta)
      (x : J) (y : J)

/-- The positive finite-volume DT Rayleigh constant persists without loss
on the ACTUAL closed orthogonal-complement restriction, for every input. -/
theorem p4Q2DU_restrictedPhysicalD12_positiveRayleigh :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : Vᗮ,
        κ * ‖x‖ ^ 2 ≤
          inner ℝ (p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta x) x := by
  obtain ⟨κ, hκ, hDT⟩ :=
    p4Q2DT_physicalTwelveDirichlet_orthogonalRayleigh H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro x
  change κ * ‖(x : J)‖ ^ 2 ≤ inner ℝ (D12 (x : J)) (x : J)
  exact hDT (x : J) x.property

/-- Pinned mathlib's invertibility of coercive real Hilbert operators
proves the ACTUAL real Banach-algebra spectrum of the restricted D12
lies in [κ(H,N,beta),∞). In particular zero lies in its resolvent set. -/
theorem p4Q2DU_restrictedPhysicalD12_spectrum_subset_Ici :
    ∃ κ : ℝ, 0 < κ ∧
      spectrum ℝ (p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta) ⊆
        Set.Ici κ := by
  let W : Submodule ℝ J :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta)ᗮ
  let D : W →L[ℝ] W :=
    p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta
  obtain ⟨κ, hκ, hRay⟩ :=
    p4Q2DU_restrictedPhysicalD12_positiveRayleigh H N hN beta hbeta
  refine ⟨κ, hκ, ?_⟩
  intro λ hλ
  change κ ≤ λ
  by_contra hnot
  have hlt : λ < κ := lt_of_not_ge hnot
  let c : ℝ≥0 := ⟨κ - λ, le_of_lt (sub_pos.mpr hlt)⟩
  have hc : 0 < c := by
    change (0 : ℝ) < κ - λ
    exact sub_pos.mpr hlt
  have hunit : IsUnit ((algebraMap ℝ (W →L[ℝ] W)) λ - D) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      ((algebraMap ℝ (W →L[ℝ] W)) λ - D) hc
    intro x
    have hbound : κ * ‖x‖ ^ 2 ≤ inner ℝ (D x) x := hRay x
    have hshift :
        inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) λ - D) x) x =
          λ * ‖x‖ ^ 2 - inner ℝ (D x) x := by
      simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hnegative :
        ‖x‖ ^ 2 * (c : ℝ) ≤
          -(inner ℝ (((algebraMap ℝ (W →L[ℝ] W)) λ - D) x) x) := by
      rw [hshift]
      change ‖x‖ ^ 2 * (κ - λ) ≤
        -(λ * ‖x‖ ^ 2 - inner ℝ (D x) x)
      nlinarith [hbound]
    exact hnegative.trans (by
      rw [Real.norm_eq_abs]
      exact neg_le_abs _)
  have hnotmem :
      λ ∉ spectrum ℝ (p4Q2DU_restrictedPhysicalD12 H N hN beta hbeta) := by
    exact (spectrum.notMem_iff).2 hunit
  exact (hnotmem hλ).elim

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
