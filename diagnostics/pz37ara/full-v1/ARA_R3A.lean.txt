import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteSpectralBudgetV5_PZ37AQZ
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARA — genuine one-slab spectral quadratic moment

The literal normalized one-slab Haar kernel controls the total squared
eigenvalues by diagonal Bessel. The existing feature factorization proves
nonnegativity of the same eigenvalues, and the true finite-volume
excitation operator norm gives a higher-moment bound. No volume-uniform
bound on the product of the two finite-volume factors is asserted.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37ARA_two_pos : 0 < (2 : ℕ) := by decide

/-- Isolate scalar and norm identities from the concrete configuration type. -/
private theorem p4Q2PZ37ARA_scaled_left {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (a : ℝ) : inner ℝ (a • x) y = a * inner ℝ x y :=
  real_inner_smul_left _ _ _

private theorem p4Q2PZ37ARA_scaled_right {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (a : ℝ) : inner ℝ x (a • y) = a * inner ℝ x y :=
  real_inner_smul_right _ _ _

private theorem p4Q2PZ37ARA_inner_swap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) : inner ℝ x y = inner ℝ y x :=
  real_inner_comm _ _

private theorem p4Q2PZ37ARA_unit_eigen_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : E →L[ℝ] E) (x : E) (a : ℝ)
    (hx : ‖x‖ = 1) (he : t x = a • x) :
    inner ℝ (t x) x = a := by
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, hx]
  ring

private theorem p4Q2PZ37ARA_unit_eigen_le_opNorm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : E →L[ℝ] E) (x : E) (a : ℝ)
    (hx : ‖x‖ = 1) (he : t x = a • x) (ha : 0 ≤ a) :
    a ≤ ‖t‖ := by
  have hn := ContinuousLinearMap.le_opNorm t x
  simpa only [he, norm_smul, hx, mul_one, Real.norm_eq_abs, abs_of_nonneg ha] using hn

private theorem p4Q2PZ37ARA_opNorm_nonneg {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : E →L[ℝ] E) : 0 ≤ ‖t‖ :=
  norm_nonneg t

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

local instance p4Q2PZ37ARA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ARA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ARA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ARA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ARA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ARA_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ARA_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ARA_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ARA_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ARA_nontrivial :
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
local notation "h2" => p4Q2PZ37ARA_two_pos

/-- The literal normalized one-slab kernel on the two-endpoint Haar space. -/
def p4Q2PZ37ARA_normalizedKernel (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  ‖T H 2 h2 beta hb‖⁻¹ • Raw H 2 h2 beta hb

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_normalizedKernel
local notation "NK" => p4Q2PZ37ARA_normalizedKernel

/-- The kernel coefficient is the genuine normalized excitation matrix
coefficient, not an unrelated model operator. -/
theorem p4Q2PZ37ARA_kernel_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g : K H 2 h2 beta hb) :
    inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb f)
      (Emb H 2 h2 beta hb g)) (NK H beta hb) =
      inner ℝ (Step H 2 h2 beta hb f) g := by
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
        p4Q2PZ37ARA_inner_swap (E := Pair H 2) _ _
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
      p4Q2PZ37ARA_scaled_right (E := Pair H 2)
        (realL2ExternalTensor f₁ g₁) (Raw H 2 h2 beta hb) _
    _ = ‖T H 2 h2 beta hb‖⁻¹ * inner ℝ (T H 2 h2 beta hb f₀) g₀ :=
      congrArg (fun z : ℝ => ‖T H 2 h2 beta hb‖⁻¹ * z) hraw
    _ = _ := (p4Q2PZ37ARA_scaled_left (E := Phys H 2)
      (T H 2 h2 beta hb f₀) g₀ _).symm

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_kernel_inner

/-- Exact normalized feature energy of a unit eigenvector. -/
theorem p4Q2PZ37ARA_eigenvalue_eq_featureEnergy
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f : K H 2 h2 beta hb) (a : ℝ)
    (hf : ‖f‖ = 1) (he : Step H 2 h2 beta hb f = a • f) :
    a = ‖T H 2 h2 beta hb‖⁻¹ * ‖A H 2 h2 beta hb (f : Phys H 2)‖^2 := by
  have hdiag : inner ℝ (Step H 2 h2 beta hb f) f = a :=
    p4Q2PZ37ARA_unit_eigen_inner (E := ↥(K H 2 h2 beta hb))
      (Step H 2 h2 beta hb) f a hf he
  rw [← hdiag]
  change inner ℝ (‖T H 2 h2 beta hb‖⁻¹ • T H 2 h2 beta hb (f : Phys H 2))
    (f : Phys H 2) = _
  calc
    _ = ‖T H 2 h2 beta hb‖⁻¹ *
        inner ℝ (T H 2 h2 beta hb (f : Phys H 2)) (f : Phys H 2) :=
      p4Q2PZ37ARA_scaled_left (E := Phys H 2)
        (T H 2 h2 beta hb (f : Phys H 2)) (f : Phys H 2) _
    _ = _ := congrArg (fun z : ℝ => ‖T H 2 h2 beta hb‖⁻¹ * z)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
        H 2 h2 beta hb (f : Phys H 2))

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_eigenvalue_eq_featureEnergy

private theorem p4Q2PZ37ARA_nonneg_of_featureEnergy (a l v : ℝ)
    (hl : 0 < l) (he : a = l⁻¹ * v^2) : 0 ≤ a := by
  rw [he]
  exact mul_nonneg (inv_nonneg.mpr hl.le) (sq_nonneg v)

private theorem p4Q2PZ37ARA_eigenvalue_nonneg_aux
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f : K H 2 h2 beta hb) (a : ℝ)
    (hf : ‖f‖ = 1) (he : Step H 2 h2 beta hb f = a • f) :
    0 ≤ a := by
  have hl : 0 < ‖T H 2 h2 beta hb‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 h2 beta hb
  have hfeature : a = ‖T H 2 h2 beta hb‖⁻¹ *
      ‖A H 2 h2 beta hb (f : Phys H 2)‖^2 :=
    p4Q2PZ37ARA_eigenvalue_eq_featureEnergy H beta hb f a hf he
  exact p4Q2PZ37ARA_nonneg_of_featureEnergy a _ _ hl hfeature

private theorem p4Q2PZ37ARA_eigenvalue_upper_aux
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f : K H 2 h2 beta hb) (a : ℝ)
    (hf : ‖f‖ = 1) (he : Step H 2 h2 beta hb f = a • f)
    (ha : 0 ≤ a) : a ≤ ‖Step H 2 h2 beta hb‖ := by
  exact @p4Q2PZ37ARA_unit_eigen_le_opNorm
    ↥(K H 2 h2 beta hb) inferInstance inferInstance
    (Step H 2 h2 beta hb) f a hf he ha

/-- Genuine eigenvalues are nonnegative and bounded by the actual
finite-volume excitation norm. -/
theorem p4Q2PZ37ARA_eigenvalue_bounds
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f : K H 2 h2 beta hb) (a : ℝ)
    (hf : ‖f‖ = 1) (he : Step H 2 h2 beta hb f = a • f) :
    0 ≤ a ∧ a ≤ ‖Step H 2 h2 beta hb‖ := by
  have ha : 0 ≤ a := p4Q2PZ37ARA_eigenvalue_nonneg_aux H beta hb f a hf he
  have hu : a ≤ ‖Step H 2 h2 beta hb‖ :=
    p4Q2PZ37ARA_eigenvalue_upper_aux H beta hb f a hf he ha
  exact ⟨ha,hu⟩

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_eigenvalue_bounds

/-- Diagonal tensor Bessel bound for every finite selection of genuine
excitation eigenvectors. The right side is the actual one-slab kernel norm. -/
theorem p4Q2PZ37ARA_finite_quadraticMoment
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^2) ≤ ‖NK H beta hb‖^2 := by
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
  have hcoef (k : ι) : inner ℝ (v k) (NK H beta hb) = rho k := by
    change inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb (b k))
      (Emb H 2 h2 beta hb (b k))) (NK H beta hb) = _
    rw [p4Q2PZ37ARA_kernel_inner]
    exact p4Q2PZ37ARA_unit_eigen_inner (E := ↥(K H 2 h2 beta hb))
      (Step H 2 h2 beta hb) (b k) (rho k) (b.orthonormal.norm_eq_one k) (he k)
  have hB := hv.sum_inner_products_le (x := NK H beta hb) (s := s)
  simpa only [hcoef, Real.norm_eq_abs, sq_abs] using hB

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_finite_quadraticMoment

/-- The full genuine quadratic spectral moment is summable at each volume,
with the same kernel budget. -/
theorem p4Q2PZ37ARA_quadraticMoment_summable
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    Summable (fun k => (rho k)^2) ∧
      (∑' k, (rho k)^2) ≤ ‖NK H beta hb‖^2 := by
  have h (s : Finset ι) := p4Q2PZ37ARA_finite_quadraticMoment H beta hb b rho he s
  have hn : 0 ≤ (fun k : ι => (rho k)^2) := fun k => sq_nonneg _
  exact ⟨summable_of_sum_le hn h, Real.tsum_le_of_sum_le hn h⟩

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_quadraticMoment_summable

private theorem p4Q2PZ37ARA_evenPower_nonneg (r : ℝ) (H : ℕ) :
    0 ≤ r^(2*H) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg r) H

private theorem p4Q2PZ37ARA_scalar_power_bound {ι : Type i}
    (s : Finset ι) (rho : ι → ℝ) (r q : ℝ) (H : ℕ)
    (h0 : ∀ k ∈ s, 0 ≤ rho k) (hr : ∀ k ∈ s, rho k ≤ r)
    (hq : (∑ k ∈ s, (rho k)^2) ≤ q) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ r^(2*H)*q :=
  (p4Q2PZ37AQZ_finite_power_le_quadratic s rho r H h0 hr).trans
    (mul_le_mul_of_nonneg_left hq (p4Q2PZ37ARA_evenPower_nonneg r H))

/-- The finite-volume spectral power budget is bounded by a product of the
true excitation contraction and the true normalized one-slab kernel budget. -/
theorem p4Q2PZ37ARA_finite_power_bound
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤
      ‖Step H 2 h2 beta hb‖^(2*H) * ‖NK H beta hb‖^2 := by
  have hr (k : ι) : 0 ≤ rho k ∧ rho k ≤ ‖Step H 2 h2 beta hb‖ :=
    p4Q2PZ37ARA_eigenvalue_bounds H beta hb (b k)
      (rho k) (b.orthonormal.norm_eq_one k) (he k)
  have hq : (∑ k ∈ s, (rho k)^2) ≤ ‖NK H beta hb‖^2 :=
    p4Q2PZ37ARA_finite_quadraticMoment H beta hb b rho he s
  exact p4Q2PZ37ARA_scalar_power_bound s rho
    ‖Step H 2 h2 beta hb‖ (‖NK H beta hb‖^2) H
    (fun k _ => (hr k).1) (fun k _ => (hr k).2) hq

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_finite_power_bound

/-- A uniform bound on this concrete product suffices for the partition
factor floor. This is a conditional criterion, not a proof of that bound. -/
theorem p4Q2PZ37ARA_partitionFloor_of_kernelBudget
    (beta : ℝ) (hb : 0 ≤ beta)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ H : ℕ, ‖Step H 2 h2 beta hb‖^(2*H) * ‖NK H beta hb‖^2 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, c ≤ PF H beta hb := by
  classical
  apply (p4Q2PZ37AQZ_partitionFloor_iff_finiteSpectralBudget beta hb).2
  refine ⟨C,hC,?_⟩
  intro H
  obtain ⟨ι,b,rho,he,_⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  refine ⟨ι,b,rho,he,?_⟩
  intro s
  exact (p4Q2PZ37ARA_finite_power_bound H beta hb b rho he s).trans (h H)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARA_partitionFloor_of_kernelBudget

end
end MGAP4D.MathlibAnalytic
