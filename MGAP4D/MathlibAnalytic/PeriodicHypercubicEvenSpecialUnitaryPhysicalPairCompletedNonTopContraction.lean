import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairAlgebraicThreeBlockContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairCompletedNonTopContractionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairCompletedNonTopContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairCompletedNonTopContractionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairCompletedNonTopContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairCompletedNonTopContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairCompletedNonTopContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairCompletedNonTopContractionSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Pythagorean combination of three pairwise orthogonal contraction bounds.
This is the finite-dimensional-looking Hilbert-space step that avoids the
factor-three loss from a triangle inequality. -/
private theorem norm_three_le_of_pairwise_orthogonal_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q : ℝ} {a b c a' b' c' : E}
    (hq : 0 ≤ q)
    (hab : inner ℝ a b = 0)
    (hac : inner ℝ a c = 0)
    (hbc : inner ℝ b c = 0)
    (hab' : inner ℝ a' b' = 0)
    (hac' : inner ℝ a' c' = 0)
    (hbc' : inner ℝ b' c' = 0)
    (ha : ‖a'‖ ≤ q * ‖a‖)
    (hb : ‖b'‖ ≤ q * ‖b‖)
    (hc : ‖c'‖ ≤ q * ‖c‖) :
    ‖a' + b' + c'‖ ≤ q * ‖a + b + c‖ := by
  have habc : inner ℝ (a + b) c = 0 := by
    rw [inner_add_left, hac, hbc, add_zero]
  have habc' : inner ℝ (a' + b') c' = 0 := by
    rw [inner_add_left, hac', hbc', add_zero]
  have hnorm :
      ‖a + b + c‖ * ‖a + b + c‖ =
        ‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ + ‖c‖ * ‖c‖ := by
    calc
      ‖a + b + c‖ * ‖a + b + c‖ =
          ‖a + b‖ * ‖a + b‖ + ‖c‖ * ‖c‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real habc
      _ = ‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ + ‖c‖ * ‖c‖ := by
        rw [norm_add_sq_eq_norm_sq_add_norm_sq_real hab]
  have hnorm' :
      ‖a' + b' + c'‖ * ‖a' + b' + c'‖ =
        ‖a'‖ * ‖a'‖ + ‖b'‖ * ‖b'‖ + ‖c'‖ * ‖c'‖ := by
    calc
      ‖a' + b' + c'‖ * ‖a' + b' + c'‖ =
          ‖a' + b'‖ * ‖a' + b'‖ + ‖c'‖ * ‖c'‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real habc'
      _ = ‖a'‖ * ‖a'‖ + ‖b'‖ * ‖b'‖ + ‖c'‖ * ‖c'‖ := by
        rw [norm_add_sq_eq_norm_sq_add_norm_sq_real hab']
  have haSq : ‖a'‖ * ‖a'‖ ≤ (q * ‖a‖) * (q * ‖a‖) :=
    mul_self_le_mul_self (norm_nonneg a') ha
  have hbSq : ‖b'‖ * ‖b'‖ ≤ (q * ‖b‖) * (q * ‖b‖) :=
    mul_self_le_mul_self (norm_nonneg b') hb
  have hcSq : ‖c'‖ * ‖c'‖ ≤ (q * ‖c‖) * (q * ‖c‖) :=
    mul_self_le_mul_self (norm_nonneg c') hc
  have hsumSq :
      ‖a'‖ * ‖a'‖ + ‖b'‖ * ‖b'‖ + ‖c'‖ * ‖c'‖ ≤
        q * q * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ + ‖c‖ * ‖c‖) := by
    calc
      ‖a'‖ * ‖a'‖ + ‖b'‖ * ‖b'‖ + ‖c'‖ * ‖c'‖ ≤
          (q * ‖a‖) * (q * ‖a‖) +
            (q * ‖b‖) * (q * ‖b‖) +
              (q * ‖c‖) * (q * ‖c‖) :=
        add_le_add (add_le_add haSq hbSq) hcSq
      _ = q * q * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ + ‖c‖ * ‖c‖) := by
        ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mp
  simp only [pow_two]
  calc
    ‖a' + b' + c'‖ * ‖a' + b' + c'‖ =
        ‖a'‖ * ‖a'‖ + ‖b'‖ * ‖b'‖ + ‖c'‖ * ‖c'‖ := hnorm'
    _ ≤ q * q * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ + ‖c‖ * ‖c‖) := hsumSq
    _ = (q * ‖a + b + c‖) * (q * ‖a + b + c‖) := by
      rw [← hnorm]
      ring

section Contraction

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "OTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan H N hN beta hbeta
local notation "TOspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan H N hN beta hbeta
local notation "OOspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan H N hN beta hbeta
local notation "Nspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- The whole algebraic non-top physical pair span contracts with the same
one-slice factor `q = ‖R‖`.  Pairwise block orthogonality is used before and
after transfer, while the double-excitation `q²` bound is absorbed by `q < 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan_normalizedTransfer_norm_le
    (x : PairE) (hx : x ∈ Nspan) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan] at hx
  rcases Submodule.mem_sup.1 hx with ⟨y, hy, c, hc, rfl⟩
  rcases Submodule.mem_sup.1 hy with ⟨a, ha, b, hb, rfl⟩
  have hab : inner ℝ a b = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_isOrtho_topOrthogonalBlockSpan
      H N hN beta hbeta a ha b hb
  have hac : inner ℝ a c = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H N hN beta hbeta a ha c hc
  have hbc : inner ℝ b c = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H N hN beta hbeta b hb c hc
  have haS : S₂ a ∈ OTspan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta ha
  have hbS : S₂ b ∈ TOspan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta hb
  have hcS : S₂ c ∈ OOspan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_invariant
      H N hN beta hbeta hc
  have habS : inner ℝ (S₂ a) (S₂ b) = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_isOrtho_topOrthogonalBlockSpan
      H N hN beta hbeta (S₂ a) haS (S₂ b) hbS
  have hacS : inner ℝ (S₂ a) (S₂ c) = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H N hN beta hbeta (S₂ a) haS (S₂ c) hcS
  have hbcS : inner ℝ (S₂ b) (S₂ c) = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H N hN beta hbeta (S₂ b) hbS (S₂ c) hcS
  have haBound : ‖S₂ a‖ ≤ ‖R‖ * ‖a‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_normalizedTransfer_norm_le
      H N hN beta hbeta a ha
  have hbBound : ‖S₂ b‖ ≤ ‖R‖ * ‖b‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_normalizedTransfer_norm_le
      H N hN beta hbeta b hb
  have hcBound2 : ‖S₂ c‖ ≤ (‖R‖ * ‖R‖) * ‖c‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan_normalizedTransfer_norm_le
      H N hN beta hbeta c hc
  have hq0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hq1 : ‖R‖ ≤ 1 :=
    le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta)
  have hqq : ‖R‖ * ‖R‖ ≤ ‖R‖ := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hcBound : ‖S₂ c‖ ≤ ‖R‖ * ‖c‖ := by
    calc
      ‖S₂ c‖ ≤ (‖R‖ * ‖R‖) * ‖c‖ := hcBound2
      _ ≤ ‖R‖ * ‖c‖ :=
        mul_le_mul_of_nonneg_right hqq (norm_nonneg c)
  rw [map_add, map_add]
  exact norm_three_le_of_pairwise_orthogonal_bounds hq0
    hab hac hbc habS hacS hbcS haBound hbBound hcBound

/-- The algebraic non-top contraction extends to the completed non-top physical
pair sector by sequential closure and continuity of normalized pair transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_norm_le
    (x : PairE) (hx : x ∈ NN) :
    ‖S₂ x‖ ≤ ‖R‖ * ‖x‖ := by
  change x ∈ Nspan.topologicalClosure at hx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hu, hux⟩
  have hSu : Tendsto (fun n => S₂ (u n)) atTop (nhds (S₂ x)) :=
    (S₂.continuous.tendsto x).comp hux
  have hleft : Tendsto (fun n => ‖S₂ (u n)‖) atTop (nhds ‖S₂ x‖) :=
    (continuous_norm.tendsto (S₂ x)).comp hSu
  have hunorm : Tendsto (fun n => ‖u n‖) atTop (nhds ‖x‖) :=
    (continuous_norm.tendsto x).comp hux
  have hright :
      Tendsto (fun n => ‖R‖ * ‖u n‖) atTop (nhds (‖R‖ * ‖x‖)) :=
    tendsto_const_nhds.mul hunorm
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun n =>
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan_normalizedTransfer_norm_le
      H N hN beta hbeta (u n) (hu n)

/-- The bundled normalized transfer on the completed non-top sector has
operator norm at most the one-slice orthogonal contraction factor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le :
    ‖SN‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound SN (norm_nonneg R)
  intro x
  change ‖S₂ (x : PairE)‖ ≤ ‖R‖ * ‖(x : PairE)‖
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_norm_le
      H N hN beta hbeta (x : PairE) x.property

/-- The completed non-top physical pair transfer is a strict finite-volume
contraction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_lt_one :
    ‖SN‖ < 1 := by
  exact lt_of_le_of_lt
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- Audit-visible completed non-top contraction package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContractionPackage :
    Prop where
  algebraicBound :
    ∀ x : PairE, x ∈ Nspan → ‖S₂ x‖ ≤ ‖R‖ * ‖x‖
  completedBound :
    ∀ x : PairE, x ∈ NN → ‖S₂ x‖ ≤ ‖R‖ * ‖x‖
  restrictedNormBound : ‖SN‖ ≤ ‖R‖
  restrictedStrict : ‖SN‖ < 1

/-- Construct the completed non-top contraction package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContractionPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContractionPackage
      H N hN beta hbeta :=
  { algebraicBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockSpan_normalizedTransfer_norm_le
        H N hN beta hbeta
    completedBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_norm_le
        H N hN beta hbeta
    restrictedNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
        H N hN beta hbeta
    restrictedStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_lt_one
        H N hN beta hbeta }

end Contraction

end

end MathlibAnalytic
end MGAP4D