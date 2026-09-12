import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorFullInverse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- The domain realization of `A - λI` for a partially defined real-linear operator.
This keeps the actual operator domain visible and does not assert continuity of `A`. -/
def realLinearPMapDomainShift
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E)
    (lambda : ℝ) :
    A.domain →ₗ[ℝ] E :=
  A.toFun - lambda • A.domain.subtype

@[simp]
theorem realLinearPMapDomainShift_zero
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E) :
    realLinearPMapDomainShift A 0 = A.toFun := by
  ext x
  simp [realLinearPMapDomainShift]

/-- Real resolvent set for an unbounded real-linear operator represented by a
`LinearPMap`.  A scalar belongs to the resolvent exactly when `A - λI` on the
actual domain has a two-sided inverse which is bounded as a map from the ambient
Hilbert carrier into the operator domain.  No continuity of the forward operator
is part of this definition.

The sign convention `A - λI` is equivalent to the usual `λI - A`, since the two
operators differ by multiplication by `-1`. -/
def realLinearPMapRealResolventSet
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E) :
    Set ℝ :=
  {lambda | ∃ R : E →L[ℝ] A.domain,
    Function.LeftInverse R (realLinearPMapDomainShift A lambda) ∧
    Function.RightInverse R (realLinearPMapDomainShift A lambda)}

/-- Real spectrum of a partially defined real-linear operator, defined as the
complement of its bounded-inverse resolvent set. -/
def realLinearPMapRealSpectrum
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E) :
    Set ℝ :=
  (realLinearPMapRealResolventSet A)ᶜ

@[simp]
theorem realLinearPMap_mem_realSpectrum_iff_not_mem_realResolventSet
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E)
    (lambda : ℝ) :
    lambda ∈ realLinearPMapRealSpectrum A ↔
      lambda ∉ realLinearPMapRealResolventSet A := by
  rfl

/-- A coercive partially defined operator with trivial kernel and full range has
zero in its real resolvent set.  The bounded inverse is the inverse constructed
from the full linear equivalence; forward continuity is never used. -/
theorem realLinearPMap_zero_mem_realResolventSet_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    0 ∈ realLinearPMapRealResolventSet A := by
  rw [realLinearPMapRealResolventSet]
  simp only [Set.mem_setOf_eq, realLinearPMapDomainShift_zero]
  let e := realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj
  let R :=
    realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
      A c hc hNorm hKer hSurj
  refine ⟨R, ?_, ?_⟩
  · intro x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · intro y
    change e (e.symm y) = y
    exact e.apply_symm_apply y

/-- Consequently zero is excluded from the real spectrum of every coercive
bijective partially defined real-linear operator. -/
theorem realLinearPMap_zero_not_mem_realSpectrum_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [Module ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    0 ∉ realLinearPMapRealSpectrum A := by
  rw [realLinearPMap_mem_realSpectrum_iff_not_mem_realResolventSet]
  exact not_not_intro
    (realLinearPMap_zero_mem_realResolventSet_of_norm_lower_bound
      A c hc hNorm hKer hSurj)

local instance osBoundaryExcitationLogGeneratorZeroResolventSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorZeroResolventSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorZeroResolventSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorZeroResolventSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorZeroResolventSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorZeroResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorZeroResolventSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorZeroResolventPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorZeroResolventSpectralSupportComplete
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

/-- The support logarithmic Hamiltonian has zero in its unbounded-operator real
resolvent set.  The witness is precisely the bounded full inverse from the
previous canonical layer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_zero_mem_realResolventSet
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ∈ realLinearPMapRealResolventSet
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta) := by
  exact
    realLinearPMap_zero_mem_realResolventSet_of_norm_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta)
      (mul_pos (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
          H N hN beta hbeta))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)

/-- Zero is not in the real spectrum of the support logarithmic Hamiltonian.
This is a statement about the support Hamiltonian, not about uniform separation
of the compact transfer spectrum from zero. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_zero_not_mem_realSpectrum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ∉ realLinearPMapRealSpectrum
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta) := by
  exact
    realLinearPMap_zero_not_mem_realSpectrum_of_norm_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta)
      (mul_pos (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
          H N hN beta hbeta))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
