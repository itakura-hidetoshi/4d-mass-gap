import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeLinearInverse
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeSurjective
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u v

/-- A partially defined real-linear map with trivial kernel and full actual range is
linearly equivalent from its actual domain to the whole codomain.  This is an
algebraic statement only: no continuity of the forward map is asserted. -/
noncomputable def realLinearPMapLinearEquiv_of_eq_zero_of_surjective
    {E : Type u}
    {F : Type v}
    [NormedAddCommGroup E]
    [Module ℝ E]
    [NormedAddCommGroup F]
    [Module ℝ F]
    (A : E →ₗ.[ℝ] F)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    A.domain ≃ₗ[ℝ] F := by
  have hInjective : Function.Injective A.toFun := by
    intro x z hxz
    have hzero : A (x - z) = 0 := by
      rw [LinearPMap.map_sub, hxz, sub_self]
    exact sub_eq_zero.mp (hKer (x - z) hzero)
  exact LinearEquiv.ofBijective A.toFun ⟨hInjective, hSurj⟩

/-- A positive lower bound for the forward partially defined operator becomes the
reciprocal upper bound for the inverse on the whole codomain once surjectivity is
known. -/
theorem realLinearPMapLinearEquiv_symm_norm_le_div_of_norm_lower_bound
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
    (hSurj : Function.Surjective A.toFun)
    (y : F) :
    ‖(((realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj).symm y :
      A.domain) : E)‖ ≤ ‖y‖ / c := by
  let e := realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj
  have hyEquiv : e (e.symm y) = y := e.apply_symm_apply y
  have hy : A (e.symm y) = y := by
    simpa [e, realLinearPMapLinearEquiv_of_eq_zero_of_surjective] using hyEquiv
  have h := hNorm (e.symm y)
  rw [hy] at h
  apply (le_div_iff₀ hc).2
  simpa [mul_comm] using h

/-- The inverse of a coercive bijective partially defined operator is a bounded
continuous linear map on the whole codomain.  The forward operator itself is not
made continuous here. -/
noncomputable def realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
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
    (hSurj : Function.Surjective A.toFun) :
    F →L[ℝ] A.domain :=
  (realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj).symm.toLinearMap.mkContinuous
    c⁻¹ (by
      intro y
      have h :=
        realLinearPMapLinearEquiv_symm_norm_le_div_of_norm_lower_bound
          A c hc hNorm hKer hSurj y
      simpa [div_eq_mul_inv, mul_comm] using h)

local instance osBoundaryExcitationLogGeneratorFullInverseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorFullInverseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorFullInverseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorFullInverseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorFullInverseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorFullInverseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorFullInverseSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorFullInversePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorFullInverseSpectralSupportComplete
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

/-- The completed one-step support logarithmic Hamiltonian is a full real-linear
equivalence from its actual operator domain onto the positive spectral-support
Hilbert carrier.  No boundedness of the forward generator is asserted. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_linearEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain ≃ₗ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta :=
  realLinearPMapLinearEquiv_of_eq_zero_of_surjective
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
      H N hN beta hbeta)

/-- The full inverse support Hamiltonian satisfies the sharp inherited finite-volume
bound `‖H_supp⁻¹ y‖ ≤ ‖y‖ / (2r)` on the entire support carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_linearEquiv_symm_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) :
    ‖(((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_linearEquiv
        H N hN beta hbeta).symm y :
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).domain) :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤
      ‖y‖ /
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) := by
  exact
    realLinearPMapLinearEquiv_symm_norm_le_div_of_norm_lower_bound
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
      y

/-- The full inverse support Hamiltonian, and only the inverse direction here, is
packaged as a continuous linear map. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_inverseContinuousLinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta →L[ℝ]
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).domain :=
  realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
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
