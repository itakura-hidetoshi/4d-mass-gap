import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCompleteExcitationParsevalV5_PZ37AQY
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQZ — exact finite spectral budget and multiplicity obstruction

AQY gives the complete genuine eigenbasis power sum at each finite volume.
Here finite sub-budgets characterize its uniform boundedness; threshold
counts preserve multiplicity. An abstract finite-family counterexample shows
that a fixed contraction alone does not imply a uniform power-sum bound.
The example is NOT asserted to be a Wilson transfer.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
universe i

private theorem p4Q2PZ37AQZ_two_pos : 0 < (2 : ℕ) := by decide

private theorem p4Q2PZ37AQZ_even_pow_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ a^(2*n) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg a) n

private theorem p4Q2PZ37AQZ_partial_sum_bound {ι : Type i} (a : ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (q : ℝ) (hs : HasSum a q) (s : Finset ι) :
    (∑ k ∈ s, a k) ≤ q :=
  sum_le_hasSum s (fun k _ => ha k) hs

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

local instance p4Q2PZ37AQZ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQZ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQZ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQZ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQZ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQZ_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37AQZ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37AQZ_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQZ_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQZ_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Exact finite-volume spectral sub-budget, on any genuine complete
eigenbasis, with its original multiplicities. -/
theorem p4Q2PZ37AQZ_finiteSpectralBudget
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 p4Q2PZ37AQZ_two_pos beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 p4Q2PZ37AQZ_two_pos beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ (PF H beta hb)⁻¹ ^ 2 - 1 := by
  classical
  have hs := p4Q2PZ37AQY_eigenbasis_power_hasSum H beta hb b rho he
  exact p4Q2PZ37AQZ_partial_sum_bound _ (fun k =>
    p4Q2PZ37AQZ_even_pow_nonneg (rho k) (H+1)) _ hs s

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_finiteSpectralBudget

/-- Every finite collection of eigenvectors above a nonnegative threshold
uses at least its cardinality times the threshold power. -/
theorem p4Q2PZ37AQZ_thresholdCount
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 p4Q2PZ37AQZ_two_pos beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 p4Q2PZ37AQZ_two_pos beta hb (b k) = rho k • b k)
    (s : Finset ι) (t : ℝ) (ht : 0 ≤ t)
    (hlarge : ∀ k ∈ s, t ≤ rho k) :
    (s.card : ℝ) * t^(2*(H+1)) ≤ (PF H beta hb)⁻¹ ^ 2 - 1 := by
  calc
    _ = ∑ _k ∈ s, t^(2*(H+1)) := by simp [nsmul_eq_mul]
    _ ≤ ∑ k ∈ s, (rho k)^(2*(H+1)) := by
      exact Finset.sum_le_sum (fun k hk =>
        pow_le_pow_left₀ ht (hlarge k hk) _)
    _ ≤ _ := p4Q2PZ37AQZ_finiteSpectralBudget H beta hb b rho he s

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_thresholdCount

/-- A uniform bound on every finite sub-budget of one complete genuine
eigenbasis per volume is equivalent to the uniform partition factor floor.
No bound on those finite sub-budgets is postulated to hold unconditionally. -/
theorem p4Q2PZ37AQZ_partitionFloor_iff_finiteSpectralBudget
    (beta : ℝ) (hb : 0 ≤ beta) :
    (∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, c ≤ PF H beta hb) ↔
      (∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ,
        ∃ (ι : Type) (b : HilbertBasis ι ℝ (K H 2 p4Q2PZ37AQZ_two_pos beta hb))
          (rho : ι → ℝ),
          (∀ k, Step H 2 p4Q2PZ37AQZ_two_pos beta hb (b k) = rho k • b k) ∧
          ∀ s : Finset ι, (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ C) := by
  classical
  rw [p4Q2PZ37AQX_partitionFloor_iff_relativeResidual_bound beta hb]
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro H
    obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
    refine ⟨ι,b,rho,he,?_⟩
    intro s
    have hpart := p4Q2PZ37AQZ_finiteSpectralBudget H beta hb b rho he s
    rw [← p4Q2PZ37AQX_relativeResidual_normSq H beta hb] at hpart
    exact hpart.trans (h H)
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro H
    obtain ⟨ι,b,rho,he,hfinite⟩ := h H
    have hs := p4Q2PZ37AQY_eigenbasis_power_hasSum H beta hb b rho he
    have hsum := hasSum_le_of_sum_le hs hfinite
    rw [p4Q2PZ37AQX_relativeResidual_normSq H beta hb]
    exact hsum

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_partitionFloor_iff_finiteSpectralBudget

/-- A separate quadratic moment bound, combined with a contraction,
controls the higher finite power sums. This is an abstract sufficient
estimate, not a volume-uniform estimate for the Wilson quadratic moment. -/
theorem p4Q2PZ37AQZ_finite_power_le_quadratic
    {ι : Type i} (s : Finset ι) (rho : ι → ℝ) (r : ℝ) (H : ℕ)
    (h0 : ∀ k ∈ s, 0 ≤ rho k) (hr : ∀ k ∈ s, rho k ≤ r) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ r^(2*H) * (∑ k ∈ s, (rho k)^2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [show 2*(H+1) = 2*H+2 by omega, pow_add]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (h0 k hk) (hr k hk) (2*H)) (sq_nonneg _)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_finite_power_le_quadratic

/-- Exact abstract multiplicity example: all eigenvalue entries are one half,
yet their power budget grows linearly. This is not a Wilson identification. -/
theorem p4Q2PZ37AQZ_halfMultiplicity_exact (H : ℕ) :
    (∑ _k ∈ Finset.range ((H+1)*4^(H+1)), ((1:ℝ)/2)^(2*(H+1))) =
      (H:ℝ)+1 := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_mul, show ((1:ℝ)/2)^2 = 1/4 by norm_num, mul_assoc, ← mul_pow]
  norm_num

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_halfMultiplicity_exact

/-- No universal uniform bound follows merely from a contraction by one
half when multiplicities may grow with volume. -/
theorem p4Q2PZ37AQZ_halfMultiplicity_noUniform :
    ¬ ∃ C : ℝ, ∀ H : ℕ,
      (∑ _k ∈ Finset.range ((H+1)*4^(H+1)), ((1:ℝ)/2)^(2*(H+1))) ≤ C := by
  rintro ⟨C,h⟩
  obtain ⟨H,hH⟩ := exists_nat_gt C
  have hh := h H
  rw [p4Q2PZ37AQZ_halfMultiplicity_exact H] at hh
  linarith

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQZ_halfMultiplicity_noUniform

end
end MGAP4D.MathlibAnalytic
