import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeClosed
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- A self-adjoint partially defined real-linear operator with trivial kernel
has dense actual range.  The proof identifies the orthogonal complement of
the range with the kernel of the adjoint, then uses self-adjointness. -/
theorem realLinearPMap_range_topologicalClosure_eq_top_of_isSelfAdjoint_of_eq_zero
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (hSelf : IsSelfAdjoint A)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) :
    (LinearMap.range A.toFun).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  have hOrth : ∀ x : A.domain, inner ℝ y (A x) = 0 := by
    intro x
    exact hy (A x) ⟨x, rfl⟩
  have hyAdj : y ∈ A.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨0, ?_⟩
    intro x
    simpa using hOrth x
  let yAdj : A.adjoint.domain := ⟨y, hyAdj⟩
  have hAdjZero : A.adjoint yAdj = 0 := by
    apply LinearPMap.adjoint_apply_eq hSelf.dense_domain yAdj
    intro x
    simpa using hOrth x
  have hAdj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hSelf
  have hyDom : y ∈ A.domain := by
    rw [← hAdj]
    exact hyAdj
  let yDom : A.domain := ⟨y, hyDom⟩
  have hAZero : A yDom = 0 := by
    have hyAdjEq : yAdj = ⟨y, by rw [hAdj]; exact hyDom⟩ := by
      apply Subtype.ext
      rfl
    rw [hyAdjEq, hAdj] at hAdjZero
    exact hAdjZero
  exact congrArg Subtype.val (hKer yDom hAZero)

local instance osBoundaryExcitationLogGeneratorRangeDenseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorRangeDenseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorRangeDenseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorRangeDenseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorRangeDenseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorRangeDenseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorRangeDenseSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorRangeDensePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorRangeDenseSpectralSupportComplete
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
is dense in the positive spectral-support Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_range_topologicalClosure_eq_top
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (LinearMap.range
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).toFun).topologicalClosure = ⊤ := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  have hSelf : IsSelfAdjoint A := by
    simpa [A,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
      using
        (realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
            H N hN beta hbeta 1 (by norm_num))
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
            H N hN beta hbeta 1))
  have hKer : ∀ x : A.domain, A x = 0 → x = 0 := by
    simpa [A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta)
  exact
    realLinearPMap_range_topologicalClosure_eq_top_of_isSelfAdjoint_of_eq_zero
      A hSelf hKer

end

end MathlibAnalytic
end MGAP4D
