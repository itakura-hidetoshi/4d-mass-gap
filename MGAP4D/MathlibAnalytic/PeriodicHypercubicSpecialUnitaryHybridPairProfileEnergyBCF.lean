import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridPairProfileBCF

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The canonical hybrid configuration is continuous in both endpoint
configurations at every fixed step. -/
theorem continuous_compact_oriented_independentPairHybridConfiguration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (k : ℕ) :
    Continuous (fun z : C.base.Configuration × C.base.Configuration =>
      C.independentPairHybridConfiguration z.1 z.2 k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridConfiguration
  apply continuous_pi
  intro target
  unfold FiniteHybridPath.configuration
  split_ifs <;> fun_prop

/-- A canonical hybrid observable increment is continuous on the independent
configuration-pair carrier. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous (C.independentPairHybridIncrementBCF target O) := by
  let k := (C.canonicalEdgeOrder target).val
  change Continuous (fun z : C.base.Configuration × C.base.Configuration =>
    O (C.independentPairHybridConfiguration z.1 z.2 (k + 1)) -
      O (C.independentPairHybridConfiguration z.1 z.2 k))
  exact
    (O.continuous.comp
      (continuous_compact_oriented_independentPairHybridConfiguration C (k + 1))).sub
    (O.continuous.comp
      (continuous_compact_oriented_independentPairHybridConfiguration C k))

/-- Every hybrid increment is bounded by twice the bounded-continuous observable
norm. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    |C.independentPairHybridIncrementBCF target O z| ≤ 2 * ‖O‖ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF
  dsimp
  calc
    |O (C.independentPairHybridConfiguration z.1 z.2
          ((C.canonicalEdgeOrder target).val + 1)) -
        O (C.independentPairHybridConfiguration z.1 z.2
          (C.canonicalEdgeOrder target).val)| ≤
        |O (C.independentPairHybridConfiguration z.1 z.2
          ((C.canonicalEdgeOrder target).val + 1))| +
        |O (C.independentPairHybridConfiguration z.1 z.2
          (C.canonicalEdgeOrder target).val)| := abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by
          simpa [Real.norm_eq_abs] using
            (O.norm_coe_le_norm
              (C.independentPairHybridConfiguration z.1 z.2
                ((C.canonicalEdgeOrder target).val + 1))))
        (by
          simpa [Real.norm_eq_abs] using
            (O.norm_coe_le_norm
              (C.independentPairHybridConfiguration z.1 z.2
                (C.canonicalEdgeOrder target).val)))
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

/-- Squared hybrid increments are integrable under the independent Gibbs-pair
probability law. -/
theorem continuous_compact_oriented_independentPairHybridIncrementBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Integrable
      (fun z => (C.independentPairHybridIncrementBCF target O z) ^ 2)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let M : ℝ := (2 * ‖O‖) ^ 2
  apply continuous_compact_oriented_integrable_of_uniform_bound
    μ
    (fun z => (C.independentPairHybridIncrementBCF target O z) ^ 2)
    ((continuous_compact_oriented_independentPairHybridIncrementBCF_continuous
      C target O).pow 2).stronglyMeasurable
    M
  intro z
  have hAbs :=
    continuous_compact_oriented_independentPairHybridIncrementBCF_abs_le
      C target O z
  have hBounds := abs_le.mp hAbs
  rw [abs_of_nonneg (sq_nonneg _)]
  dsimp [M]
  nlinarith [norm_nonneg O]

/-- Mean-square energy of one canonical hybrid increment under two independent
Gibbs configurations. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∫ z, (C.independentPairHybridIncrementBCF target O z) ^ 2
    ∂(C.gibbsMeasure.prod C.gibbsMeasure)

/-- Canonical hybrid increment energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridIncrementEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
  exact integral_nonneg fun _ => sq_nonneg _

/-- Link-indexed square-root profile generated by the canonical independent-pair
hybrid path. The edge-cardinality factor is the finite Cauchy--Schwarz cost. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  Real.sqrt
    ((Fintype.card C.base.geometry.Edge : ℝ) *
      C.independentPairHybridIncrementEnergyBCF target O)

/-- The square of the canonical hybrid profile is exactly edge cardinality times
its increment energy. -/
theorem continuous_compact_oriented_independentPairHybridProfileBCF_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (C.independentPairHybridProfileBCF target O) ^ 2 =
      (Fintype.card C.base.geometry.Edge : ℝ) *
        C.independentPairHybridIncrementEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridProfileBCF
  exact Real.sq_sqrt <|
    mul_nonneg (Nat.cast_nonneg _)
      (continuous_compact_oriented_independentPairHybridIncrementEnergyBCF_nonneg
        C target O)

/-- The canonical hybrid profile automatically satisfies the global independent
Gibbs-pair majorant required by the first field of the pair-residual profile. -/
theorem continuous_compact_oriented_gibbsIndependentPairDifferenceEnergyBCF_le_sum_hybridProfile_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.gibbsIndependentPairDifferenceEnergyBCF O ≤
      ∑ target : C.base.geometry.Edge,
        (C.independentPairHybridProfileBCF target O) ^ 2 := by
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  have hLeftInt : Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        (O z.1 - O z.2) ^ 2) μ := by
    let M : ℝ := (2 * ‖O‖) ^ 2
    apply continuous_compact_oriented_integrable_of_uniform_bound
      μ
      (fun z : C.base.Configuration × C.base.Configuration =>
        (O z.1 - O z.2) ^ 2)
      (((O.continuous.comp continuous_fst).sub
        (O.continuous.comp continuous_snd)).pow 2).stronglyMeasurable
      M
    intro z
    have hAbs : |O z.1 - O z.2| ≤ 2 * ‖O‖ := by
      calc
        |O z.1 - O z.2| ≤ |O z.1| + |O z.2| := abs_sub _ _
        _ ≤ ‖O‖ + ‖O‖ := by
          exact add_le_add
            (by simpa [Real.norm_eq_abs] using (O.norm_coe_le_norm z.1))
            (by simpa [Real.norm_eq_abs] using (O.norm_coe_le_norm z.2))
        _ = 2 * ‖O‖ := (two_mul ‖O‖).symm
    have hBounds := abs_le.mp hAbs
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp [M]
    nlinarith [norm_nonneg O]
  have hEachInt : ∀ target : C.base.geometry.Edge,
      Integrable
        (fun z => (C.independentPairHybridIncrementBCF target O z) ^ 2) μ :=
    fun target => by
      simpa [μ] using
        continuous_compact_oriented_independentPairHybridIncrementBCF_sq_integrable
          C target O
  have hSumInt : Integrable
      (fun z => ∑ target : C.base.geometry.Edge,
        (C.independentPairHybridIncrementBCF target O z) ^ 2) μ := by
    exact integrable_finset_sum _ fun target _ => hEachInt target
  have hRightInt : Integrable
      (fun z => (Fintype.card C.base.geometry.Edge : ℝ) *
        ∑ target : C.base.geometry.Edge,
          (C.independentPairHybridIncrementBCF target O z) ^ 2) μ :=
    hSumInt.const_mul _
  have hIntegrated := integral_mono hLeftInt hRightInt
    (fun z =>
      continuous_compact_oriented_independentPairDifference_sq_le_card_mul_sum_hybridIncrement_sq
        C O z.1 z.2)
  have hGlobalLe :
      C.gibbsIndependentPairDifferenceEnergyBCF O ≤
        (Fintype.card C.base.geometry.Edge : ℝ) *
          ∑ target : C.base.geometry.Edge,
            C.independentPairHybridIncrementEnergyBCF target O := by
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsIndependentPairDifferenceEnergyBCF
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementEnergyBCF
    calc
      (∫ z : C.base.Configuration × C.base.Configuration,
          (O z.1 - O z.2) ^ 2 ∂μ) ≤
          ∫ z, (Fintype.card C.base.geometry.Edge : ℝ) *
            ∑ target : C.base.geometry.Edge,
              (C.independentPairHybridIncrementBCF target O z) ^ 2 ∂μ :=
        hIntegrated
      _ = (Fintype.card C.base.geometry.Edge : ℝ) *
          ∫ z, ∑ target : C.base.geometry.Edge,
            (C.independentPairHybridIncrementBCF target O z) ^ 2 ∂μ := by
        rw [integral_const_mul]
      _ = (Fintype.card C.base.geometry.Edge : ℝ) *
          ∑ target : C.base.geometry.Edge,
            ∫ z, (C.independentPairHybridIncrementBCF target O z) ^ 2 ∂μ := by
        rw [integral_finset_sum _ (fun target _ => hEachInt target)]
  calc
    C.gibbsIndependentPairDifferenceEnergyBCF O ≤
        (Fintype.card C.base.geometry.Edge : ℝ) *
          ∑ target : C.base.geometry.Edge,
            C.independentPairHybridIncrementEnergyBCF target O := hGlobalLe
    _ = ∑ target : C.base.geometry.Edge,
        (Fintype.card C.base.geometry.Edge : ℝ) *
          C.independentPairHybridIncrementEnergyBCF target O := by
      rw [Finset.mul_sum]
    _ = ∑ target : C.base.geometry.Edge,
        (C.independentPairHybridProfileBCF target O) ^ 2 := by
      apply Finset.sum_congr rfl
      intro target _
      exact
        (continuous_compact_oriented_independentPairHybridProfileBCF_sq
          C target O).symm

end

end MathlibAnalytic
end MGAP4D
