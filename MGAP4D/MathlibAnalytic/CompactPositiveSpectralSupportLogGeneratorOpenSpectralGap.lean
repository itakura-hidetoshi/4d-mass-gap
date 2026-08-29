import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorZeroResolvent
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- The bounded inverse of a coercive bijective partially defined operator,
viewed on the ambient carrier rather than on the operator domain. -/
noncomputable def realLinearPMapAmbientInverse_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    E →L[ℝ] E :=
  A.domain.subtypeL.comp
    (realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
      A c hc hNorm hKer hSurj)

/-- The ambient inverse inherits the reciprocal coercive operator-norm bound. -/
theorem realLinearPMapAmbientInverse_norm_le_inv_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    ‖realLinearPMapAmbientInverse_of_norm_lower_bound A c hc hNorm hKer hSurj‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr hc.le
  · intro y
    change
      ‖(((realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
          A c hc hNorm hKer hSurj) y : A.domain) : E)‖ ≤ c⁻¹ * ‖y‖
    have h :=
      realLinearPMapLinearEquiv_symm_norm_le_div_of_norm_lower_bound
        A c hc hNorm hKer hSurj y
    simpa [div_eq_mul_inv, mul_comm] using h

/-- The ambient inverse is a right inverse of `A` on the actual operator domain. -/
theorem realLinearPMapAmbientInverse_apply_operator
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (x : A.domain) :
    realLinearPMapAmbientInverse_of_norm_lower_bound A c hc hNorm hKer hSurj (A x) = (x : E) := by
  let e := realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj
  change ((e.symm (e x) : A.domain) : E) = (x : E)
  exact congrArg Subtype.val (e.symm_apply_apply x)

/-- The operator applied to its bounded domain-valued inverse is the identity. -/
theorem realLinearPMap_operator_apply_inverse
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (y : E) :
    A ((realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
      A c hc hNorm hKer hSurj) y) = y := by
  let e := realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj
  change e (e.symm y) = y
  exact e.apply_symm_apply y

/-- Every real scalar of modulus strictly below the coercive constant belongs to
the unbounded-operator real resolvent set.  The inverse is obtained by the
Neumann factorization
`(A - λI)⁻¹ = A⁻¹ (I - λ A⁻¹)⁻¹`.
No continuity of the forward operator is used. -/
theorem realLinearPMap_mem_realResolventSet_of_abs_lt_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    lambda ∈ realLinearPMapRealResolventSet A := by
  let R : E →L[ℝ] A.domain :=
    realLinearPMapLinearEquiv_symmContinuousLinearMap_of_norm_lower_bound
      A c hc hNorm hKer hSurj
  let B : E →L[ℝ] E :=
    realLinearPMapAmbientInverse_of_norm_lower_bound A c hc hNorm hKer hSurj
  have hBR (z : E) : B z = ((R z : A.domain) : E) := by
    rfl
  have hB : ‖B‖ ≤ c⁻¹ :=
    realLinearPMapAmbientInverse_norm_le_inv_of_norm_lower_bound
      A c hc hNorm hKer hSurj
  have hscaled : ‖lambda • B‖ < 1 := by
    calc
      ‖lambda • B‖ = |lambda| * ‖B‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |lambda| * c⁻¹ := mul_le_mul_of_nonneg_left hB (abs_nonneg lambda)
      _ < c * c⁻¹ := by
        exact mul_lt_mul_of_pos_right hlambda (inv_pos.mpr hc)
      _ = 1 := by exact mul_inv_cancel₀ (ne_of_gt hc)
  let U : (E →L[ℝ] E)ˣ := Units.oneSub (lambda • B) hscaled
  let S : E →L[ℝ] E := (↑(U⁻¹) : E →L[ℝ] E)
  let Rlambda : E →L[ℝ] A.domain := R.comp S
  have hSleft : S * (1 - lambda • B) = 1 := by
    change (↑(U⁻¹) : E →L[ℝ] E) * (↑U : E →L[ℝ] E) = 1
    exact U.inv_mul
  have hSright : (1 - lambda • B) * S = 1 := by
    change (↑U : E →L[ℝ] E) * (↑(U⁻¹) : E →L[ℝ] E) = 1
    exact U.mul_inv
  rw [realLinearPMapRealResolventSet]
  refine ⟨Rlambda, ?_, ?_⟩
  · intro x
    have hfactor : realLinearPMapDomainShift A lambda x = (1 - lambda • B) (A x) := by
      simp [realLinearPMapDomainShift, B,
        realLinearPMapAmbientInverse_apply_operator A c hc hNorm hKer hSurj x,
        sub_eq_add_neg]
    rw [hfactor]
    have hcancel : S ((1 - lambda • B) (A x)) = A x := by
      have h := congrArg (fun T : E →L[ℝ] E => T (A x)) hSleft
      simpa using h
    change R (S ((1 - lambda • B) (A x))) = x
    rw [hcancel]
    let e := realLinearPMapLinearEquiv_of_eq_zero_of_surjective A hKer hSurj
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · intro y
    have hcancel : (1 - lambda • B) (S y) = y := by
      have h := congrArg (fun T : E →L[ℝ] E => T y) hSright
      simpa using h
    have hfactor :
        realLinearPMapDomainShift A lambda (Rlambda y) =
          (1 - lambda • B) (S y) := by
      simp [realLinearPMapDomainShift, Rlambda, R,
        realLinearPMap_operator_apply_inverse A c hc hNorm hKer hSurj,
        hBR, sub_eq_add_neg]
    rw [hfactor, hcancel]

/-- Hence the real spectrum of a coercive bijective partially defined operator
avoids the whole open interval `(-c,c)`. -/
theorem realLinearPMap_realSpectrum_disjoint_Ioo_neg_pos_of_norm_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun) :
    Disjoint (realLinearPMapRealSpectrum A) (Ioo (-c) c) := by
  rw [Set.disjoint_left]
  intro lambda hs hgap
  have habs : |lambda| < c := (abs_lt).2 hgap
  have hres :=
    realLinearPMap_mem_realResolventSet_of_abs_lt_norm_lower_bound
      A c hc hNorm hKer hSurj lambda habs
  exact ((realLinearPMap_mem_realSpectrum_iff_not_mem_realResolventSet A lambda).1 hs) hres

local instance osBoundaryExcitationLogGeneratorOpenGapSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorOpenGapSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorOpenGapSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorOpenGapSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorOpenGapSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorOpenGapSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorOpenGapSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorOpenGapPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorOpenGapSpectralSupportNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance

local instance osBoundaryExcitationLogGeneratorOpenGapSpectralSupportComplete
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

/-- Every real scalar of modulus less than the coercive support gap `2r` belongs
to the support logarithmic Hamiltonian resolvent set. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_mem_realResolventSet_of_abs_lt_two_decayRate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    lambda ∈ realLinearPMapRealResolventSet
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta) := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    infer_instance
  exact
    realLinearPMap_mem_realResolventSet_of_abs_lt_norm_lower_bound
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
      lambda hlambda

/-- Quantitative open spectral gap for the completed support logarithmic Hamiltonian:
its real spectrum is disjoint from `(-2r,2r)`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_realSpectrum_disjoint_open_two_decayRate_gap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Disjoint
      (realLinearPMapRealSpectrum
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta))
      (Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)) := by
  letI : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    infer_instance
  exact
    realLinearPMap_realSpectrum_disjoint_Ioo_neg_pos_of_norm_lower_bound
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
