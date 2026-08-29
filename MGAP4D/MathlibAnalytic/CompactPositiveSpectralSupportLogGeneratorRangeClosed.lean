import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeLinearInverse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Module End Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u v

/-- A closed partially defined real-linear operator which is bounded below by a
strictly positive constant has closed actual range.  No continuity of the
forward unbounded operator is assumed: convergence of range vectors forces
Cauchy convergence of their domain preimages, and closedness of the graph
then identifies the limit. -/
theorem realLinearPMap_range_isClosed_of_isClosed_of_norm_lower_bound
    {E : Type u}
    {F : Type v}
    [NormedAddCommGroup E]
    [Module ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F]
    [Module ℝ F]
    (A : E →ₗ.[ℝ] F)
    (c : ℝ)
    (hc : 0 < c)
    (hClosed : A.IsClosed)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖) :
    IsClosed (LinearMap.range A.toFun : Set F) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y z hy hz
  choose x hx using hy
  have hyCauchy : CauchySeq y := hz.cauchySeq
  have hxCauchy : CauchySeq (fun n => (x n : E)) := by
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hyCauchy) (c * eps) (mul_pos hc heps)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hLower := hNorm (x m - x n)
    have hRange : A (x m - x n) = y m - y n := by
      rw [LinearPMap.map_sub]
      change A.toFun (x m) - A.toFun (x n) = y m - y n
      rw [hx m, hx n]
    rw [hRange] at hLower
    have hLower' : c * ‖((x m : E) - (x n : E))‖ ≤ ‖y m - y n‖ := by
      simpa using hLower
    have hY : ‖y m - y n‖ < c * eps := by
      simpa [dist_eq_norm] using hN m hm n hn
    have hX : ‖((x m : E) - (x n : E))‖ < eps := by
      nlinarith
    simpa [dist_eq_norm] using hX
  obtain ⟨xlim, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hAlim : Tendsto (fun n => A (x n)) atTop (𝓝 z) := by
    convert hz using 1
    funext n
    exact hx n
  have hPair :
      Tendsto (fun n => ((x n : E), A (x n))) atTop (𝓝 (xlim, z)) :=
    hxlim.prodMk_nhds hAlim
  have hGraph : (xlim, z) ∈ (A.graph : Set (E × F)) :=
    hClosed.mem_of_tendsto hPair
      (Eventually.of_forall fun n =>
        (LinearPMap.mem_graph_iff A).2 ⟨x n, rfl, rfl⟩)
  rcases (LinearPMap.mem_graph_iff A).1 hGraph with ⟨xDomain, hxDomain, hAx⟩
  exact ⟨xDomain, hAx⟩

local instance osBoundaryExcitationLogGeneratorRangeClosedSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorRangeClosedSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorRangeClosedSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorRangeClosedSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorRangeClosedSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorRangeClosedSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorRangeClosedSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorRangeClosedPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorRangeClosedSpectralSupportComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact
    (realHilbertZeroEigenspaceSupport_isClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)).completeSpace_coe

/-- The actual range of the completed one-step support logarithmic Hamiltonian
is a closed subspace of the positive spectral-support Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_range_isClosed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsClosed
      (LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta).toFun :
        Set
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)) := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hClosed : A.IsClosed := by
    simpa [A,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
      using
        (realHilbertCompactPositiveZeroSupportLogGenerator_isClosed
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
            H N hN beta hbeta 1 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
            H N hN beta hbeta 1))
  have hNorm : ∀ x : A.domain, c * ‖(x :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤ ‖A x‖ := by
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta)
  exact realLinearPMap_range_isClosed_of_isClosed_of_norm_lower_bound A c hc hClosed hNorm

end

end MathlibAnalytic
end MGAP4D
