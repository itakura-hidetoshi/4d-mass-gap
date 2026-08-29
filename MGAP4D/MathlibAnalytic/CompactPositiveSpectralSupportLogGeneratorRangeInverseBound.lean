import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorNormCoercive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u v

/-- An injective partially defined linear map with a norm lower bound has a
unique quantitatively controlled preimage for every point of its actual
range.  This is deliberately a range-level receipt: no surjectivity onto the
whole codomain is assumed. -/
theorem realLinearPMap_existsUnique_preimage_on_range_of_norm_lower_bound
    {E : Type u}
    {F : Type v}
    [NormedAddCommGroup E]
    [Module ℝ E]
    [NormedAddCommGroup F]
    [Module ℝ F]
    (A : E →ₗ.[ℝ] F)
    (c : ℝ)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (y : LinearMap.range A.toFun) :
    ∃! x : A.domain,
      A x = (y : F) ∧ c * ‖(x : E)‖ ≤ ‖(y : F)‖ := by
  have hInjective : Function.Injective A := by
    intro x z hxz
    have hzero : A (x - z) = 0 := by
      rw [LinearPMap.map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hKer (x - z) hzero)
  rcases y.property with ⟨x, hx⟩
  have hx' : A x = (y : F) := hx
  have hxNorm : c * ‖(x : E)‖ ≤ ‖(y : F)‖ := by
    have h := hNorm x
    rw [hx'] at h
    exact h
  refine ⟨x, ⟨hx', hxNorm⟩, ?_⟩
  intro z hz
  exact hInjective (hz.1.trans hx'.symm)

local instance osBoundaryExcitationLogGeneratorRangeInverseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorRangeInverseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorRangeInverseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorRangeInverseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorRangeInverseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorRangeInverseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorRangeInverseSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorRangeInversePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Every vector in the actual range of the completed one-step support
logarithmic Hamiltonian has a unique domain preimage, quantitatively bounded
by the finite-volume gap coefficient `2r`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_existsUnique_preimage_on_range
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : LinearMap.range
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).toFun) :
    ∃! x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta x =
        (y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) ∧
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta *
        ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ ≤
        ‖(y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ := by
  apply realLinearPMap_existsUnique_preimage_on_range_of_norm_lower_bound
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
