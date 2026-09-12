import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryCanonicalBackgroundProfileBCF
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridSourceOverlapTransportEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The fixed-left overlap fiber energy at canonical rank `k`, kept as a function
of the original independent Gibbs configuration pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (k : ℕ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.singleLinkConditionalOverlapObservableTransportEnergyBCF
    (C.independentPairHybridConfiguration z.1 z.2 k)
    (C.independentPairHybridConfiguration z.1 z.2 (k + 1))
    (C.independentPairHybridConfiguration z.1 z.2 k)
    target O

/-- At every valid canonical rank, the endpoint-pair map for the selected
physical source is exactly the consecutive canonical hybrid pair. -/
@[simp]
theorem continuous_compact_oriented_independentPairHybridEndpointPairMap_hybridTargetTrajectorySourceAtRank_of_lt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridEndpointPairMap
        (C.hybridTargetTrajectorySourceAtRank target k) (A, B) =
      (C.independentPairHybridConfiguration A B k,
        C.independentPairHybridConfiguration A B (k + 1)) := by
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPreEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridPostEndpointMap,
      ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank,
      hk]

/-- Exact Gibbs-pair pullback of one canonical fixed-left overlap fiber: its
integral is the existing source-indexed overlap transport energy for the physical
source occupying rank `k`. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_canonicalFixedLeftOverlapFiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF
        target (C.hybridTargetTrajectorySourceAtRank target k) O =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  let source := C.hybridTargetTrajectorySourceAtRank target k
  have hJoint :=
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportIntegrandBCF_integrable
      C target source O
  have hFiberIntegrable : Integrable
      (fun y : C.base.Configuration × C.base.Configuration =>
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          y.1 y.2 y.1 target O)
      (C.independentPairHybridEndpointPairMeasure source) := by
    simpa
      [source,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportMeasure,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportIntegrandBCF,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF,
        continuous_compact_oriented_configurationPairConditionalOverlapCouplingKernel_apply]
      using hJoint.integral_compProd
  change C.independentPairHybridSourceOverlapTransportEnergyBCF target source O = _
  rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_fiber]
  calc
    (∫ y : C.base.Configuration × C.base.Configuration,
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          y.1 y.2 y.1 target O
        ∂C.independentPairHybridEndpointPairMeasure source) =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.singleLinkConditionalOverlapObservableTransportEnergyBCF
          (C.independentPairHybridEndpointPairMap source z).1
          (C.independentPairHybridEndpointPairMap source z).2
          (C.independentPairHybridEndpointPairMap source z).1
          target O
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
          unfold
            ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMeasure
          exact MeasureTheory.integral_map
            (continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
              C source).aemeasurable
            hFiberIntegrable.aestronglyMeasurable
    _ = ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            unfold
              ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
            change
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                  (C.independentPairHybridEndpointPairMap source z).1
                  (C.independentPairHybridEndpointPairMap source z).2
                  (C.independentPairHybridEndpointPairMap source z).1
                  target O =
                C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                  (C.independentPairHybridConfiguration z.1 z.2 k)
                  (C.independentPairHybridConfiguration z.1 z.2 (k + 1))
                  (C.independentPairHybridConfiguration z.1 z.2 k)
                  target O
            rw [show source =
              C.hybridTargetTrajectorySourceAtRank target k from rfl]
            rw [continuous_compact_oriented_independentPairHybridEndpointPairMap_hybridTargetTrajectorySourceAtRank_of_lt
              C z.1 z.2 target k hk]

/-- Summing the exact rankwise pullbacks over a finite canonical prefix converts
the full fixed-left Gibbs-pair fiber budget into the corresponding sum of the
existing source-indexed overlap energies. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_eq_sum_integral_canonicalFixedLeftOverlapFiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    (∑ k ∈ Finset.range m,
      C.independentPairHybridSourceOverlapTransportEnergyBCF
        target (C.hybridTargetTrajectorySourceAtRank target k) O) =
      ∑ k ∈ Finset.range m,
        ∫ z : C.base.Configuration × C.base.Configuration,
          C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
            target O k z
          ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  apply Finset.sum_congr rfl
  intro k hkRange
  exact
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_canonicalFixedLeftOverlapFiber
      C target O k
      (lt_of_lt_of_le (Finset.mem_range.mp hkRange) hm)

end

end MathlibAnalytic
end MGAP4D
