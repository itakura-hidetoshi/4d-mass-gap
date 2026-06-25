import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolvent
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A closed operator with a coercive real shift has closed shifted range.

If shifted images converge, coercivity makes the underlying domain vectors a
Cauchy sequence.  Completeness supplies an ambient limit.  Reconstructing the
unshifted images and using graph closedness puts the limit back in the operator
domain. -/
theorem realShift_isClosed_range
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hClosed : A.IsClosed)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    _root_.IsClosed (LinearMap.range (A.realShift lambda) : Set E) := by
  refine IsSeqClosed.isClosed ?_
  intro ySeq y hyRange hyTendsto
  choose x hx using hyRange
  have hyCauchy : CauchySeq ySeq := hyTendsto.cauchySeq
  have hxCauchy : CauchySeq (fun n => (x n : E)) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    have hpositive : 0 < mass - lambda := sub_pos.mpr hlambda
    obtain ⟨N, hN⟩ :=
      (Metric.cauchySeq_iff.mp hyCauchy)
        ((mass - lambda) * epsilon) (mul_pos hpositive hepsilon)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hbound := A.realShift_norm_lower_bound hlambda hgap (x m - x n)
    have hshift :
        A.realShift lambda (x m - x n) = ySeq m - ySeq n := by
      calc
        A.realShift lambda (x m - x n) =
            A.realShift lambda (x m) - A.realShift lambda (x n) :=
          (A.realShift lambda).map_sub (x m) (x n)
        _ = ySeq m - ySeq n := by rw [hx m, hx n]
    rw [hshift] at hbound
    have hyclose := hN m hm n hn
    rw [dist_eq_norm] at hyclose ⊢
    have hmul :
        (mass - lambda) * ‖(((x m - x n : A.domain) : E))‖ <
          (mass - lambda) * epsilon :=
      lt_of_le_of_lt hbound hyclose
    nlinarith
  obtain ⟨xLimit, hxLimit⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hAeq (n : ℕ) :
      A (x n) = ySeq n + lambda • (x n : E) := by
    calc
      A (x n) =
          (A (x n) - lambda • (x n : E)) + lambda • (x n : E) := by
        abel
      _ = ySeq n + lambda • (x n : E) := by
        rw [← A.realShift_apply, hx n]
  have hATendsto :
      Tendsto (fun n => A (x n)) atTop
        (𝓝 (y + lambda • xLimit)) := by
    simpa only [hAeq] using hyTendsto.add (hxLimit.const_smul lambda)
  have hPairTendsto :
      Tendsto (fun n => ((x n : E), A (x n))) atTop
        (𝓝 (xLimit, y + lambda • xLimit)) := by
    simpa only [nhds_prod_eq] using hxLimit.prodMk hATendsto
  have hGraphClosed : _root_.IsClosed (A.graph : Set (E × E)) := hClosed
  have hGraphMem : (xLimit, y + lambda • xLimit) ∈ A.graph :=
    hGraphClosed.mem_of_tendsto hPairTendsto
      (Eventually.of_forall fun n => A.mem_graph (x n))
  rcases (A.mem_graph_iff).mp hGraphMem with
    ⟨xDomain, hxBase, hxValue⟩
  refine ⟨xDomain, ?_⟩
  calc
    A.realShift lambda xDomain =
        A xDomain - lambda • (xDomain : E) :=
      A.realShift_apply lambda xDomain
    _ = (y + lambda • xLimit) - lambda • xLimit := by
      rw [hxValue, hxBase]
    _ = y := by abel

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every excitation-sector real shift below the transferred mass has closed
range. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealShift_isClosed_range
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    _root_.IsClosed
      (LinearMap.range
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :
          Set P.VacuumOrthogonalHilbert) := by
  apply LinearPMap.realShift_isClosed_range
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hClosed :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed
        hP hSelf)
    hlambda
  intro y
  simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
      ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) y

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
