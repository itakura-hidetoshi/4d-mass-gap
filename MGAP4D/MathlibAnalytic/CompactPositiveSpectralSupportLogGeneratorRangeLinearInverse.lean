import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeInverseBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u v

/-- An injective partially defined real-linear map is linearly equivalent to its
actual range.  This is purely algebraic and does not assert boundedness of the
forward map. -/
noncomputable def realLinearPMapRangeLinearEquiv_of_eq_zero
    {E : Type u}
    {F : Type v}
    [NormedAddCommGroup E]
    [Module ℝ E]
    [NormedAddCommGroup F]
    [Module ℝ F]
    (A : E →ₗ.[ℝ] F)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) :
    A.domain ≃ₗ[ℝ] LinearMap.range A.toFun := by
  have hInjective : Function.Injective A := by
    intro x z hxz
    have hzero : A (x - z) = 0 := by
      rw [LinearPMap.map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hKer (x - z) hzero)
  apply LinearEquiv.ofBijective A.toFun.rangeRestrict
  constructor
  · intro x z hxz
    apply hInjective
    exact congrArg Subtype.val hxz
  · intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- The inverse of the range-restricted equivalence inherits the reciprocal
norm bound from a positive lower bound for the original partially defined
operator. -/
theorem realLinearPMapRangeLinearEquiv_symm_norm_le_div_of_norm_lower_bound
    {E : Type u}
    {F : Type v}
    [NormedAddCommGroup E]
    [Module ℝ E]
    [NormedAddCommGroup F]
    [Module ℝ F]
    (A : E →ₗ.[ℝ] F)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (y : LinearMap.range A.toFun) :
    ‖(((realLinearPMapRangeLinearEquiv_of_eq_zero A hKer).symm y : A.domain) : E)‖ ≤
      ‖(y : F)‖ / c := by
  let e := realLinearPMapRangeLinearEquiv_of_eq_zero A hKer
  have hyRange : e (e.symm y) = y := e.apply_symm_apply y
  have hy : A (e.symm y) = (y : F) := by
    exact congrArg Subtype.val hyRange
  have h := hNorm (e.symm y)
  rw [hy] at h
  apply (le_div_iff₀ hc).2
  simpa [mul_comm] using h

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorRangeLinearInverseSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorRangeLinearInversePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed one-step support logarithmic Hamiltonian is algebraically a
linear equivalence from its domain onto its actual range. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_rangeLinearEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain ≃ₗ[ℝ]
      LinearMap.range
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta).toFun :=
  realLinearPMapRangeLinearEquiv_of_eq_zero
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta)

/-- The inverse on the actual range has operator-size bound `1 / (2r)` in the
ambient support Hilbert norm.  This is not a whole-codomain inverse claim. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_rangeLinearEquiv_symm_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : LinearMap.range
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).toFun) :
    ‖(((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_rangeLinearEquiv
        H N hN beta hbeta).symm y :
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).domain) :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤
      ‖(y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ /
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) := by
  apply realLinearPMapRangeLinearEquiv_symm_norm_le_div_of_norm_lower_bound
  · exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
