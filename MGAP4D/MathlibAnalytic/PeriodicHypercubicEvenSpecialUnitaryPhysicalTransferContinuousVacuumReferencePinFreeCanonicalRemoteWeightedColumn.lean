import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeWeightedRemoteResponseFamily
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Canonical remote weighted column from arbitrary response families

The preceding theorem bounds every arbitrary target-indexed family of literal
remote fixed-right responses by one pin-free aggregate resolvent.

The canonical response profile is defined pointwise as the supremum of those
literal response values.  Because the remote target set is finite and every
center weight is strictly positive for s >= 1, we may choose, independently at
each remote target, a literal response value arbitrarily close to its canonical
supremum.  Applying the arbitrary-family theorem and then sending the
approximation error to zero lifts the response-family estimate to the canonical
weighted remote column.

No common maximizing witness is assumed.  No target-cardinality factor
survives in the final estimate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance pinFreeCanonicalRemoteWeightedColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Since every literal response value is nonnegative and the value set is
nonempty, the auxiliary max with zero in the canonical profile is inactive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_eq_sSup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source =
      sSup
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
          H N hN beta hbeta target source) := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hNonempty :
      S.Nonempty :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
      H N hN beta hbeta target source
  rcases hNonempty with ⟨x, hx⟩
  have hXSup : x ≤ sSup S :=
    le_csSup
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_bddAbove
        H N hN beta hbeta target source)
      hx
  have hXNonneg : 0 ≤ x := by
    rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
    exact abs_nonneg _
  have hSupNonneg : 0 ≤ sSup S := hXNonneg.trans hXSup
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
  change max 0 (sSup S) = sSup S
  exact max_eq_right hSupNonneg

/-- Under a strict pin-free weighted-column hypothesis on the canonical profile,
its geometrically remote weighted column satisfies the pin-free aggregate
resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_remoteExponentialWeightedColumn_le_pinFreeAggregateResolvent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1) :
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source center
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let Rcan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let S :=
    fun target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
        H N hN beta hbeta target source
  let K : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        W source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹
  have hRNonneg : ∀ target source, 0 ≤ Rcan target source := by
    simpa [Rcan] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta
  have hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta Rcan := by
    simpa [Rcan] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
        H N hN beta hbeta
  have hWOne :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H, 1 ≤ W target := by
    intro target
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_one_le
        H s hs center target
  have hWPos :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H, 0 < W target := by
    intro target
    exact zero_lt_one.trans_le (hWOne target)
  have hProfileSup :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        Rcan target source = sSup (S target) := by
    intro target
    simpa [Rcan, S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_eq_sSup
        H N hN beta hbeta target source
  have hSNonempty :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H, (S target).Nonempty := by
    intro target
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
        H N hN beta hbeta target source
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let cardScale : ℝ := (remote.card : ℝ) + 1
  have hCardScale : 0 < cardScale := by
    dsimp [cardScale]
    positivity
  let delta :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      ε / (cardScale * W target)
  have hDeltaPos :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H, 0 < delta target := by
    intro target
    dsimp [delta]
    exact div_pos hε (mul_pos hCardScale (hWPos target))
  have hApproxExists :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ∃ x : ℝ,
          x ∈ S target ∧
            sSup (S target) < x + delta target := by
    intro target
    have hBelow :
        sSup (S target) - delta target < sSup (S target) :=
      sub_lt_self _ (hDeltaPos target)
    obtain ⟨x, hx, hxLower⟩ :=
      exists_lt_of_lt_csSup (hSNonempty target) hBelow
    refine ⟨x, hx, ?_⟩
    linarith
  choose x hxMem hxApprox using hApproxExists
  have hWitness :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ∃
          (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ),
          x target =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
              H N hN beta hbeta B target source g₁ g₂ h k := by
    intro target
    simpa [S] using hxMem target
  choose B g₁ g₂ h k hxWitnessEq using hWitness
  have hDeltaCancel :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        W target * delta target = ε / cardScale := by
    intro target
    dsimp [delta]
    field_simp [ne_of_gt hCardScale, ne_of_gt (hWPos target)]
    <;> ring
  have hErrorSum :
      (∑ target ∈ remote, W target * delta target) ≤ ε := by
    have hCardNonneg : 0 ≤ (remote.card : ℝ) := by positivity
    have hCardFrac :
        (remote.card : ℝ) / cardScale ≤ 1 := by
      rw [div_le_one hCardScale]
      dsimp [cardScale]
      linarith
    calc
      (∑ target ∈ remote, W target * delta target) =
          (remote.card : ℝ) * (ε / cardScale) := by
            simp_rw [hDeltaCancel]
            simp [nsmul_eq_mul]
      _ = ε * ((remote.card : ℝ) / cardScale) := by
            ring
      _ ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left hCardFrac hε.le
      _ = ε := by ring
  have hTermApprox :
      ∀ target ∈ remote,
        W target * Rcan target source ≤
          W target * x target + W target * delta target := by
    intro target _hTarget
    calc
      W target * Rcan target source =
          W target * sSup (S target) := by
            rw [hProfileSup target]
      _ ≤ W target * (x target + delta target) :=
        (mul_lt_mul_of_pos_left (hxApprox target) (hWPos target)).le
      _ = W target * x target + W target * delta target := by
        ring
  have hApproxSum :
      (∑ target ∈ remote, W target * Rcan target source) ≤
        (∑ target ∈ remote, W target * x target) + ε := by
    calc
      (∑ target ∈ remote, W target * Rcan target source) ≤
          ∑ target ∈ remote,
            (W target * x target + W target * delta target) := by
              apply Finset.sum_le_sum
              intro target hTarget
              exact hTermApprox target hTarget
      _ =
          (∑ target ∈ remote, W target * x target) +
            (∑ target ∈ remote, W target * delta target) := by
              simp only [Finset.sum_add_distrib]
      _ ≤ (∑ target ∈ remote, W target * x target) + ε :=
        add_le_add_left hErrorSum _
  have hFamily :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteWeightedResponseFamily_le_pinFreeAggregateResolvent
      H N hN beta hbeta s hs center source Rcan hRNonneg hUniform
      responseCoefficient hResponseCoefficient
      (by simpa [Rcan] using hResponseWeighted)
      hCoefficientLtOne B g₁ g₂ h k
  have hWitnessSum :
      (∑ target ∈ remote, W target * x target) ≤ K := by
    calc
      (∑ target ∈ remote, W target * x target) =
          ∑ target ∈ remote,
            W target *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
                H N hN beta hbeta (B target) target source
                (g₁ target) (g₂ target) (h target) (k target) := by
                  apply Finset.sum_congr rfl
                  intro target _hTarget
                  rw [hxWitnessEq target]
      _ ≤ K := by
        simpa [remote, W, Rcan, K] using hFamily
  calc
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta target source) =
      ∑ target ∈ remote, W target * Rcan target source := by
        rfl
    _ ≤ (∑ target ∈ remote, W target * x target) + ε := hApproxSum
    _ ≤ K + ε := add_le_add_right hWitnessSum ε
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ + ε := by
      rfl

end

end MathlibAnalytic
end MGAP4D
