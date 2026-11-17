import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureExactVacuumFeatureDensityV5_PZ37ANB
import Mathlib.Tactic

/-!
# PZ37ANB — mutual absolute continuity of original periodic Wilson positive closure

The exact original normalized finite periodic SU(N) Gibbs positive-closure
marginal is boundaryHaar.prod positiveHaar with the positive, measurable
density ENNReal.ofReal (boundaryVacuumMoment(b) * completedGramFeature(b,x)).

Thus the genuine full-periodic marginal and unchanged product Haar have exactly
the same null sets. No temporal-gauge equality to the ANA half-path law,
abstract OS Hilbert identification, one-slab intertwining, or continuum limit
is assumed or asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANB_closureAC_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance p4Q2PZ37ANB_closureAC_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37ANB_closureAC_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37ANB_closureAC_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37ANB_closureAC_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37ANB_closureAC_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The genuine full-periodic positive-closure Gibbs probability is absolutely
continuous with respect to the original boundary/open-half product Haar. -/
theorem p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_ac_productHaar
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure ≪
      (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  rw [p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal_eq_vacuum_mul_feature]
  exact withDensity_absolutelyContinuous _ _

/-- Since the certified boundary vacuum and completed Gram feature
are both pointwise strictly positive, product Haar is absolutely continuous
with respect to the genuine periodic interacting positive-closure marginal.

No uniform density lower bound is required and no original model is altered. -/
theorem p4Q2PZ37ANB_positiveClosureProductHaar_ac_fullPeriodicGibbs
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N) ≪
      Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  let μ :=
    (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)
  let w :
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal
      (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta z.1 *
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2)
  have hw : Measurable w := by
    have hb : Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
          periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta z.1) :=
      (periodicHypercubicEvenBoundaryVacuumMoment_measurable
        H N hN beta hbeta).comp measurable_fst
    have hx : Measurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta z.1 z.2) :=
      periodicHypercubicEvenBoundaryVacuumGramFeature_measurable
        H N hN beta hbeta
    exact ENNReal.measurable_ofReal.comp (hb.mul hx)
  have hw_ne_zero : ∀ᵐ z ∂μ, w z ≠ 0 := by
    filter_upwards [] with z
    change ENNReal.ofReal
      (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta z.1 *
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta z.1 z.2) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (mul_pos
        (periodicHypercubicEvenBoundaryVacuumMoment_pos
          H N hN beta hbeta z.1)
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
          H N hN beta hbeta z.1 z.2)))
  rw [p4Q2PZ37ANB_fullPeriodicGibbs_positiveClosure_marginal_eq_vacuum_mul_feature]
  change μ ≪ μ.withDensity w
  exact withDensity_absolutelyContinuous' hw.aemeasurable hw_ne_zero

/-- The true periodic Gibbs positive closure and original product Haar
have the same null sets at every finite H, without any OS identification. -/
theorem p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_mutuallyAC_productHaar
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure ≪
      (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) ∧
    ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N) ≪
      Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) := by
  exact ⟨
    p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_ac_productHaar
      H N hN beta hbeta,
    p4Q2PZ37ANB_positiveClosureProductHaar_ac_fullPeriodicGibbs
      H N hN beta hbeta⟩

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_ac_productHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_positiveClosureProductHaar_ac_fullPeriodicGibbs
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_mutuallyAC_productHaar
