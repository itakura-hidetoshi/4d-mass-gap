import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorRemoteDoobBoundedTestInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance continuousVacuumSameColorRemoteMajorantObstructionSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumSameColorRemoteMajorantObstructionIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumSameColorRemoteMajorantObstructionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumSameColorRemoteMajorantObstructionSecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumSameColorRemoteMajorantObstructionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumSameColorRemoteMajorantObstructionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumSameColorRemoteMajorantObstructionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Distinct links in the same six-color class as `target`.

This is the exact finite source set over which one would naively sum the
single-source bound from the continuous-vacuum Doob comparison. -/
noncomputable def periodicHypercubicEvenSpatialSliceSameColorRemoteLinks
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter fun source =>
    periodicHypercubicEvenSpatialSliceLinkColor H source =
        periodicHypercubicEvenSpatialSliceLinkColor H target ∧
      source ≠ target

@[simp]
theorem periodicHypercubicEvenSpatialSlice_mem_sameColorRemoteLinks_iff
    (H : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    source ∈ periodicHypercubicEvenSpatialSliceSameColorRemoteLinks H target ↔
      periodicHypercubicEvenSpatialSliceLinkColor H source =
          periodicHypercubicEvenSpatialSliceLinkColor H target ∧
        source ≠ target := by
  classical
  simp [periodicHypercubicEvenSpatialSliceSameColorRemoteLinks]

/-- The uniform bounded-test majorant furnished by the current one-source
continuous-vacuum Doob theorem. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorant
    (beta : ℝ) : ℝ :=
  2 * ((Real.exp (16 * beta) - 1) / (Real.exp (16 * beta) + 1))

/-- Membership in the same-color remote source set is exactly enough to invoke
the current single-source bounded-test comparison.

The conclusion remains a one-source statement.  In particular, this theorem
does not assert block factorization, Doob commutation, or any volume-independent
row-sum estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemote_boundedTest_influence_of_mem
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hsource : source ∈
      periodicHypercubicEvenSpatialSliceSameColorRemoteLinks H target)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let targetEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
    let sourceEdge := periodicHypercubicEvenSpatialSliceLinkEmbedding H source
    let Ah := C.base.replaceLink A sourceEdge h
    let Ak := C.base.replaceLink A sourceEdge k
    |(∫ g, phi g ∂C.singleLinkDoobConditionalMeasure Omega Ah targetEdge) -
      (∫ g, phi g ∂C.singleLinkDoobConditionalMeasure Omega Ak targetEdge)| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorant
        beta := by
  have hremote :=
    (periodicHypercubicEvenSpatialSlice_mem_sameColorRemoteLinks_iff
      H target source).1 hsource
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorant] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_boundedTest_influence
      H N hN beta hbeta
      (target := target) (source := source)
      hremote.1.symm hremote.2.symm A h k phi hphi hphiBound)

/-- The row sum obtained by assigning the same available one-source bounded-test
majorant to every distinct source in the target's six-color class. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorantRowSum
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) : ℝ :=
  ∑ _source in periodicHypercubicEvenSpatialSliceSameColorRemoteLinks H target,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorant
      beta

/-- The naive aggregation of the present single-source bound carries the
cardinality of the full remote same-color class exactly.

This is an obstruction statement about the *available constant majorant*, not a
claim that the true Doob influence row sum has this value.  Therefore the
single-source estimate alone cannot erase volume dependence: an additional
mechanism such as decay, cancellation, factorization, or a block estimate is
needed before a volume-independent color contraction can be concluded. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorantRowSum_eq_card_nsmul
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorantRowSum
        H target beta =
      (periodicHypercubicEvenSpatialSliceSameColorRemoteLinks H target).card •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorant
          beta := by
  classical
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColorRemoteBoundedTestMajorantRowSum]

end

end MathlibAnalytic
end MGAP4D
