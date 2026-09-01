import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentFiniteEigenmode
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativeCompletionEquiv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology

noncomputable section

local instance osExcitationPairHilbertImageClosureSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osExcitationPairHilbertImageClosureSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osExcitationPairHilbertImageClosureSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osExcitationPairHilbertImageClosureSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osExcitationPairHilbertImageClosureSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osExcitationPairHilbertImageClosureSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osExcitationPairHilbertImageClosureSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- If every algebraic physical excitation kernel is already in the canonical
completed finite Wilson OS image, then the whole completed excitation sector is
in that image.  The only analytic input is closedness of the actual OS image;
the excitation sector itself is the closure of the algebraic tensor image. -/
theorem exists_completedOSState_of_excitationPairHilbertSector_of_algebraicRange
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (hAlgebraic :
      Set.range
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            (halfExtent n) N hN (beta n) (hbeta n)) ⊆
        Set.range (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n))
    (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      (halfExtent n) N hN (beta n) (hbeta n)) :
    ∃ phi : (R.approximatingPreHilbertDataAt n).PhysicalHilbert,
      R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n phi =
        (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2
          (halfExtent n) N) := by
  have hxClosure :
      (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2
          (halfExtent n) N) ∈
        closure
          (Set.range
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
              (halfExtent n) N hN (beta n) (hbeta n))) := by
    simpa only [
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector,
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairAlgebraicRange,
        Submodule.topologicalClosure_coe,
        LinearMap.coe_range] using x.property
  have hClosed :
      IsClosed
        (Set.range (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n)) :=
    R.isClosed_range_toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n
  exact (closure_minimal hAlgebraic hClosed) hxClosure

/-- Consequently every vector in the native Hilbert completion of the physical
excitation tensor core has an actual finite Wilson OS state with exactly the
same concrete pair-`L²` realization.  The lift preserves the norm because both
the native completion equivalence and the OS boundary realization are linear
isometries. -/
theorem exists_completedOSState_of_nativeExcitationCompletion_of_algebraicRange
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent N hN beta hbeta)
    (n : ℕ)
    (hAlgebraic :
      Set.range
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            (halfExtent n) N hN (beta n) (hbeta n)) ⊆
        Set.range (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n))
    (z : UniformSpace.Completion
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        (halfExtent n) N hN (beta n) (hbeta n))) :
    ∃ phi : (R.approximatingPreHilbertDataAt n).PhysicalHilbert,
      R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n phi =
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
              (halfExtent n) N hN (beta n) (hbeta n) z :
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              (halfExtent n) N hN (beta n) (hbeta n)) :
            PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2
              (halfExtent n) N) ∧
        ‖phi‖ = ‖z‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
      (halfExtent n) N hN (beta n) (hbeta n)
  obtain ⟨phi, hphi⟩ :=
    R.exists_completedOSState_of_excitationPairHilbertSector_of_algebraicRange
      n hAlgebraic (E z)
  refine ⟨phi, hphi, ?_⟩
  calc
    ‖phi‖ = ‖R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n phi‖ := by
      symm
      exact (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n).norm_map phi
    _ = ‖((E z :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            (halfExtent n) N hN (beta n) (hbeta n)) :
          PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairL2
            (halfExtent n) N)‖ := by rw [hphi]
    _ = ‖E z‖ := rfl
    _ = ‖z‖ := E.norm_map z

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection

end

end MathlibAnalytic
end MGAP4D
