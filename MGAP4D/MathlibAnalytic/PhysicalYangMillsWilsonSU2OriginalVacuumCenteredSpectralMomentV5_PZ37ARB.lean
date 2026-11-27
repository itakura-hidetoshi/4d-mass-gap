import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneSlabQuadraticSpectralMomentV5_PZ37ARA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARB — vacuum-centered genuine one-slab kernel budget

Subtract the rank-one tensor of the same nonnegative physical top
eigenvector used in AQW/AQX. The ambient Haar kernel loses exactly one
unit of squared norm. Excitation coefficients are unchanged. No claim
that the ambient centered kernel belongs to the physical double
excitation carrier, or that the resulting budget is volume-uniform.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37ARB_two_pos : 0 < (2 : ℕ) := by decide

/-- Isolate scalar and norm identities from the concrete configuration type. -/
private theorem p4Q2PZ37ARB_scaled_left {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (a : ℝ) : inner ℝ (a • x) y = a * inner ℝ x y :=
  real_inner_smul_left _ _ _

private theorem p4Q2PZ37ARB_scaled_right {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (a : ℝ) : inner ℝ x (a • y) = a * inner ℝ x y :=
  real_inner_smul_right _ _ _

private theorem p4Q2PZ37ARB_inner_swap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : inner ℝ x y = inner ℝ y x :=
  real_inner_comm _ _

private theorem p4Q2PZ37ARB_unit_eigen_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : E →L[ℝ] E) (x : E) (a : ℝ)
    (hx : ‖x‖ = 1) (he : t x = a • x) :
    inner ℝ (t x) x = a := by
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, hx]
  ring

private theorem p4Q2PZ37ARB_remove_unit_normSq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v y : E) (hv : ‖v‖ = 1) (hvy : inner ℝ v y = 1) :
    ‖y-v‖^2 = ‖y‖^2-1 := by
  have hyv : inner ℝ y v = 1 := (real_inner_comm v y).trans hvy
  rw [norm_sub_sq_real, hyv, hv]
  ring

private theorem p4Q2PZ37ARB_inner_sub_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y v : E) (h : inner ℝ x v = 0) :
    inner ℝ x (y-v) = inner ℝ x y := by
  rw [inner_sub_right,h,sub_zero]

private theorem p4Q2PZ37ARB_normalized_fixed_aux {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : E →L[ℝ] E) (o : E) (l : ℝ) (hl : l ≠ 0)
    (he : t o = l • o) : l⁻¹ • t o = o := by
  rw [he,smul_smul,inv_mul_cancel₀ hl,one_smul]

private theorem p4Q2PZ37ARB_unit_self_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (o : E) (ho : ‖o‖ = 1) : inner ℝ o o = 1 := by
  rw [real_inner_self_eq_norm_sq,ho]
  norm_num

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Pair" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
local notation "Dec" => periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "OO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure
local notation "EH" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "PF" => p4Q2PZ37AQW_partitionFactor
local notation "Res" => p4Q2PZ37AQX_relativeResidual
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry

local instance p4Q2PZ37ARB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ARB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ARB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ARB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ARB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ARB_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ARB_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ARB_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ARB_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ARB_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "A" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
local notation "Raw" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
local notation "h2" => p4Q2PZ37ARB_two_pos

local notation "NK" => p4Q2PZ37ARA_normalizedKernel
local notation "Omega" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
local notation "F" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
local notation "S" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator

/-- Rank-one tensor of the genuine nonnegative top eigenvector. -/
def p4Q2PZ37ARB_vacuumTensor (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  Dec H 2 (Omega H 2 h2 beta hb) (Omega H 2 h2 beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_vacuumTensor
local notation "V" => p4Q2PZ37ARB_vacuumTensor

/-- Genuine normalized Haar kernel with its unit vacuum tensor removed. -/
def p4Q2PZ37ARB_centeredKernel (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  NK H beta hb - V H beta hb

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_centeredKernel
local notation "CK" => p4Q2PZ37ARB_centeredKernel

private theorem p4Q2PZ37ARB_pair_inner (H : ℕ) (f g x y : Phys H 2) :
    inner ℝ (Dec H 2 f g) (Dec H 2 x y) = inner ℝ f x * inner ℝ g y :=
  realL2ExternalTensor_inner (f : Lp ℝ 2 (Mu H 2)) (x : Lp ℝ 2 (Mu H 2))
    (g : Lp ℝ 2 (Mu H 2)) (y : Lp ℝ 2 (Mu H 2))

/-- The ARA kernel coefficient identity extends to every physical test pair,
including the genuine vacuum. -/
theorem p4Q2PZ37ARB_physical_kernel_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : Phys H 2) :
    inner ℝ (Dec H 2 f g) (NK H beta hb) =
      inner ℝ (S H 2 h2 beta hb f) g := by
  let f₀ : Phys H 2 := f
  let g₀ : Phys H 2 := g
  let f₁ : Lp ℝ 2 (Mu H 2) := f₀
  let g₁ : Lp ℝ 2 (Mu H 2) := g₀
  change inner ℝ (realL2ExternalTensor f₁ g₁)
    (‖T H 2 h2 beta hb‖⁻¹ • Raw H 2 h2 beta hb) =
    inner ℝ (‖T H 2 h2 beta hb‖⁻¹ • T H 2 h2 beta hb f₀) g₀
  have hraw : inner ℝ (realL2ExternalTensor f₁ g₁) (Raw H 2 h2 beta hb) =
      inner ℝ (T H 2 h2 beta hb f₀) g₀ := by
    calc
      _ = inner ℝ (Raw H 2 h2 beta hb) (realL2ExternalTensor f₁ g₁) :=
        p4Q2PZ37ARB_inner_swap (E := Pair H 2) _ _
      _ = realL2HilbertSchmidtKernelPairing (Raw H 2 h2 beta hb) f₁ g₁ := rfl
      _ = inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H 2 h2 beta hb f₁) g₁ :=
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
          H 2 h2 beta hb f₁ g₁).symm
      _ = _ := by
        change inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
            H 2 h2 beta hb f₁) g₁ =
          inner ℝ ((T H 2 h2 beta hb f₀ : Phys H 2) : Lp ℝ 2 (Mu H 2)) g₁
        exact congrArg (fun z : Lp ℝ 2 (Mu H 2) => inner ℝ z g₁)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_coe
            H 2 h2 beta hb f₀).symm
  calc
    _ = ‖T H 2 h2 beta hb‖⁻¹ *
        inner ℝ (realL2ExternalTensor f₁ g₁) (Raw H 2 h2 beta hb) :=
      p4Q2PZ37ARB_scaled_right (E := Pair H 2)
        (realL2ExternalTensor f₁ g₁) (Raw H 2 h2 beta hb) _
    _ = ‖T H 2 h2 beta hb‖⁻¹ * inner ℝ (T H 2 h2 beta hb f₀) g₀ :=
      congrArg (fun z : ℝ => ‖T H 2 h2 beta hb‖⁻¹ * z) hraw
    _ = _ := (p4Q2PZ37ARB_scaled_left (E := Phys H 2)
      (T H 2 h2 beta hb f₀) g₀ _).symm


#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_physical_kernel_inner

theorem p4Q2PZ37ARB_vacuumTensor_norm
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    ‖V H beta hb‖ = 1 := by
  let o := Omega H 2 h2 beta hb
  have ho : ‖o‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 h2 beta hb
  have ht := realL2ExternalTensor_norm
    (o : Lp ℝ 2 (Mu H 2)) (o : Lp ℝ 2 (Mu H 2))
  change ‖V H beta hb‖ = ‖o‖ * ‖o‖ at ht
  calc
    _ = ‖o‖ * ‖o‖ := ht
    _ = 1 := by rw [ho,one_mul]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_vacuumTensor_norm

theorem p4Q2PZ37ARB_vacuumTensor_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    inner ℝ (V H beta hb) (NK H beta hb) = 1 := by
  let o := Omega H 2 h2 beta hb
  have ho : ‖o‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm H 2 h2 beta hb
  have hl : 0 < ‖T H 2 h2 beta hb‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H 2 h2 beta hb
  have he : T H 2 h2 beta hb o = ‖T H 2 h2 beta hb‖ • o :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen H 2 h2 beta hb
  have hs : S H 2 h2 beta hb o = o :=
    p4Q2PZ37ARB_normalized_fixed_aux (E := Phys H 2)
      (T H 2 h2 beta hb) o _ hl.ne' he
  calc
    _ = inner ℝ (S H 2 h2 beta hb o) o :=
      p4Q2PZ37ARB_physical_kernel_inner H beta hb o o
    _ = inner ℝ o o := congrArg (fun z : Phys H 2 => inner ℝ z o) hs
    _ = 1 := p4Q2PZ37ARB_unit_self_inner (E := Phys H 2) o ho

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_vacuumTensor_inner

/-- Subtract exactly the squared norm of the unit vacuum, not an estimate. -/
theorem p4Q2PZ37ARB_centered_normSq
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    ‖CK H beta hb‖^2 = ‖NK H beta hb‖^2 - 1 :=
  p4Q2PZ37ARB_remove_unit_normSq (E := Pair H 2)
    (V H beta hb) (NK H beta hb)
    (p4Q2PZ37ARB_vacuumTensor_norm H beta hb)
    (p4Q2PZ37ARB_vacuumTensor_inner H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_centered_normSq

/-- Orthogonality to the full top eigenspace removes the vacuum contribution
without changing any excitation matrix coefficient. -/
theorem p4Q2PZ37ARB_centered_excitation_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : K H 2 h2 beta hb) :
    inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb f)
      (Emb H 2 h2 beta hb g)) (CK H beta hb) =
      inner ℝ (Step H 2 h2 beta hb f) g := by
  let o := Omega H 2 h2 beta hb
  have ho : o ∈ F H 2 h2 beta hb := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector]
    exact Submodule.mem_span_singleton_self _
  have hf := f.property
  change (f : Phys H 2) ∈ (F H 2 h2 beta hb)ᗮ at hf
  have hz : inner ℝ (f : Phys H 2) o = 0 :=
    Submodule.inner_left_of_mem_orthogonal ho hf
  have hpair : inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb f)
      (Emb H 2 h2 beta hb g)) (V H beta hb) = 0 := by
    change inner ℝ (Dec H 2 (f : Phys H 2) (g : Phys H 2)) (Dec H 2 o o) = 0
    rw [p4Q2PZ37ARB_pair_inner,hz,zero_mul]
  calc
    _ = inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb f)
        (Emb H 2 h2 beta hb g)) (NK H beta hb) :=
      p4Q2PZ37ARB_inner_sub_zero (E := Pair H 2) _
        (NK H beta hb) (V H beta hb) hpair
    _ = _ := p4Q2PZ37ARA_kernel_inner H beta hb f g

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_centered_excitation_inner

/-- All finite diagonal spectral budgets are controlled by the centered
genuine kernel, with the vacuum already removed. -/
theorem p4Q2PZ37ARB_finite_centered_quadratic
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^2) ≤ ‖CK H beta hb‖^2 := by
  classical
  let v : ι → Pair H 2 := fun k =>
    realL2ExternalTensor (Emb H 2 h2 beta hb (b k)) (Emb H 2 h2 beta hb (b k))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro k l
    change inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb (b k))
      (Emb H 2 h2 beta hb (b k)))
      (realL2ExternalTensor (Emb H 2 h2 beta hb (b l))
      (Emb H 2 h2 beta hb (b l))) = _
    rw [realL2ExternalTensor_inner]
    change inner ℝ (b k) (b l) * inner ℝ (b k) (b l) = _
    rw [(orthonormal_iff_ite.mp b.orthonormal) k l]
    by_cases h : k = l <;> simp [h]
  have hcoef (k : ι) : inner ℝ (v k) (CK H beta hb) = rho k := by
    change inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb (b k))
      (Emb H 2 h2 beta hb (b k))) (CK H beta hb) = _
    rw [p4Q2PZ37ARB_centered_excitation_inner]
    exact p4Q2PZ37ARB_unit_eigen_inner (E := ↥(K H 2 h2 beta hb))
      (Step H 2 h2 beta hb) (b k) (rho k) (b.orthonormal.norm_eq_one k) (he k)
  have hB := hv.sum_inner_products_le (x := CK H beta hb) (s := s)
  simpa only [hcoef, Real.norm_eq_abs, sq_abs] using hB


#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_finite_centered_quadratic

/-- The full quadratic moment now has the strictly sharper vacuum-subtracted
budget. No ambient-to-physical carrier equality is assumed. -/
theorem p4Q2PZ37ARB_centered_quadratic_tsum
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    (∑' k, (rho k)^2) ≤ ‖NK H beta hb‖^2 - 1 := by
  have h (s : Finset ι) := p4Q2PZ37ARB_finite_centered_quadratic H beta hb b rho he s
  have hn : 0 ≤ (fun k : ι => (rho k)^2) := fun k => sq_nonneg _
  have ht := Real.tsum_le_of_sum_le hn h
  rw [p4Q2PZ37ARB_centered_normSq H beta hb] at ht
  exact ht

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_centered_quadratic_tsum

private theorem p4Q2PZ37ARB_evenPower_nonneg (r : ℝ) (H : ℕ) :
    0 ≤ r^(2*H) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg r) H

private theorem p4Q2PZ37ARB_scalar_power_bound {ι : Type i}
    (s : Finset ι) (rho : ι → ℝ) (r q : ℝ) (H : ℕ)
    (h0 : ∀ k ∈ s, 0 ≤ rho k) (hr : ∀ k ∈ s, rho k ≤ r)
    (hq : (∑ k ∈ s, (rho k)^2) ≤ q) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ r^(2*H)*q :=
  (p4Q2PZ37AQZ_finite_power_le_quadratic s rho r H h0 hr).trans
    (mul_le_mul_of_nonneg_left hq (p4Q2PZ37ARB_evenPower_nonneg r H))

theorem p4Q2PZ37ARB_finite_centered_power
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤
      ‖Step H 2 h2 beta hb‖^(2*H) * ‖CK H beta hb‖^2 := by
  have hr (k : ι) : 0 ≤ rho k ∧ rho k ≤ ‖Step H 2 h2 beta hb‖ :=
    p4Q2PZ37ARA_eigenvalue_bounds H beta hb (b k)
      (rho k) (b.orthonormal.norm_eq_one k) (he k)
  have hq : (∑ k ∈ s, (rho k)^2) ≤ ‖CK H beta hb‖^2 :=
    p4Q2PZ37ARB_finite_centered_quadratic H beta hb b rho he s
  exact p4Q2PZ37ARB_scalar_power_bound s rho
    ‖Step H 2 h2 beta hb‖ (‖CK H beta hb‖^2) H
    (fun k _ => (hr k).1) (fun k _ => (hr k).2) hq

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_finite_centered_power

/-- Explicit finite-volume residual budget, combining the actual
one-slab centered kernel with AQY's complete eigenbasis. -/
theorem p4Q2PZ37ARB_relative_budget_bound
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    (PF H beta hb)⁻¹ ^ 2 - 1 ≤
      ‖Step H 2 h2 beta hb‖^(2*H) * (‖NK H beta hb‖^2-1) := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have hfinite (s : Finset ι) :=
    p4Q2PZ37ARB_finite_centered_power H beta hb b rho he s
  have h := hasSum_le_of_sum_le hs hfinite
  rw [p4Q2PZ37ARB_centered_normSq H beta hb] at h
  exact h

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_relative_budget_bound

/-- Conditional uniform partition floor using the vacuum-subtracted
one-slab budget. The uniform estimate remains an independent obligation. -/
theorem p4Q2PZ37ARB_partitionFloor_of_centeredBudget
    (beta : ℝ) (hb : 0 ≤ beta)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ H : ℕ, ‖Step H 2 h2 beta hb‖^(2*H) * (‖NK H beta hb‖^2-1) ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, c ≤ PF H beta hb := by
  apply (p4Q2PZ37AQX_partitionFloor_iff_relativeResidual_bound beta hb).2
  refine ⟨C,hC,?_⟩
  intro H
  rw [p4Q2PZ37AQX_relativeResidual_normSq H beta hb]
  exact (p4Q2PZ37ARB_relative_budget_bound H beta hb).trans (h H)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARB_partitionFloor_of_centeredBudget

end
end MGAP4D.MathlibAnalytic
