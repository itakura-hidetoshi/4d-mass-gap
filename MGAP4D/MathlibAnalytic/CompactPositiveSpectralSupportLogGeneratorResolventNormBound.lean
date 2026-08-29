import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorOpenSpectralGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- A resolvent point lying strictly inside a coercive gap admits a bounded inverse
with the sharp elementary coercive estimate `‖Rλ‖ ≤ (c - |λ|)⁻¹`.

The proof uses only the actual-domain identity `(A - λI) Rλ = I`, coercivity of
`A`, and the triangle inequality. In particular, no boundedness or continuity of
the forward operator `A` is assumed. -/
theorem realLinearPMap_exists_resolventInverse_norm_le_of_mem_and_abs_lt
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (hres : lambda ∈ realLinearPMapRealResolventSet A) :
    ∃ Rlambda : E →L[ℝ] A.domain,
      Function.LeftInverse Rlambda (realLinearPMapDomainShift A lambda) ∧
      Function.RightInverse Rlambda (realLinearPMapDomainShift A lambda) ∧
      ‖Rlambda‖ ≤ (c - |lambda|)⁻¹ := by
  have hgap : 0 < c - |lambda| := sub_pos.mpr hlambda
  rw [realLinearPMapRealResolventSet] at hres
  rcases hres with ⟨Rlambda, hleft, hright⟩
  refine ⟨Rlambda, hleft, hright, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr hgap.le
  · intro y
    have hshiftLower :
        (c - |lambda|) * ‖((Rlambda y : A.domain) : E)‖ ≤
          ‖realLinearPMapDomainShift A lambda (Rlambda y)‖ := by
      have htriangle :
          ‖A (Rlambda y)‖ ≤
            ‖realLinearPMapDomainShift A lambda (Rlambda y)‖ +
              |lambda| * ‖((Rlambda y : A.domain) : E)‖ := by
        calc
          ‖A (Rlambda y)‖ =
              ‖realLinearPMapDomainShift A lambda (Rlambda y) +
                lambda • ((Rlambda y : A.domain) : E)‖ := by
            congr 1
            simp [realLinearPMapDomainShift]
          _ ≤ ‖realLinearPMapDomainShift A lambda (Rlambda y)‖ +
                ‖lambda • ((Rlambda y : A.domain) : E)‖ := norm_add_le _ _
          _ = ‖realLinearPMapDomainShift A lambda (Rlambda y)‖ +
                |lambda| * ‖((Rlambda y : A.domain) : E)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      linarith [hNorm (Rlambda y)]
    rw [hright y] at hshiftLower
    change ‖Rlambda y‖ ≤ (c - |lambda|)⁻¹ * ‖y‖
    have hdiv : ‖Rlambda y‖ ≤ ‖y‖ / (c - |lambda|) := by
      apply (le_div_iff₀ hgap).2
      simpa [mul_comm] using hshiftLower
    simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- Quantitative resolvent norm estimate generated directly from coercivity and
the Neumann resolvent existence theorem. -/
theorem realLinearPMap_exists_resolventInverse_norm_le_of_abs_lt_norm_lower_bound
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
    ∃ Rlambda : E →L[ℝ] A.domain,
      Function.LeftInverse Rlambda (realLinearPMapDomainShift A lambda) ∧
      Function.RightInverse Rlambda (realLinearPMapDomainShift A lambda) ∧
      ‖Rlambda‖ ≤ (c - |lambda|)⁻¹ := by
  exact
    realLinearPMap_exists_resolventInverse_norm_le_of_mem_and_abs_lt
      A c hNorm lambda hlambda
      (realLinearPMap_mem_realResolventSet_of_abs_lt_norm_lower_bound
        A c hc hNorm hKer hSurj lambda hlambda)

/-- Ambient realization of the actual-domain resolvent inverse.  This is useful for
concrete unbounded operators because its codomain is the ambient Banach space while
the witnesses still record both inverse identities on the genuine domain. -/
theorem realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
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
    lambda ∈ realLinearPMapRealResolventSet A ∧
      ∃ Blambda : E →L[ℝ] E,
        (∀ x : A.domain,
          Blambda (realLinearPMapDomainShift A lambda x) = (x : E)) ∧
        (∀ y : E, ∃ x : A.domain,
          realLinearPMapDomainShift A lambda x = y ∧ Blambda y = (x : E)) ∧
        ‖Blambda‖ ≤ (c - |lambda|)⁻¹ := by
  have hres :=
    realLinearPMap_mem_realResolventSet_of_abs_lt_norm_lower_bound
      A c hc hNorm hKer hSurj lambda hlambda
  refine ⟨hres, ?_⟩
  rcases
    realLinearPMap_exists_resolventInverse_norm_le_of_mem_and_abs_lt
      A c hNorm lambda hlambda hres with
    ⟨Rlambda, hleft, hright, hRnorm⟩
  let Blambda : E →L[ℝ] E := A.domain.subtypeL.comp Rlambda
  refine ⟨Blambda, ?_, ?_, ?_⟩
  · intro x
    change ((Rlambda (realLinearPMapDomainShift A lambda x) : A.domain) : E) = (x : E)
    exact congrArg Subtype.val (hleft x)
  · intro y
    refine ⟨Rlambda y, hright y, ?_⟩
    rfl
  · have hgap : 0 < c - |lambda| := sub_pos.mpr hlambda
    apply ContinuousLinearMap.opNorm_le_bound
    · exact inv_nonneg.mpr hgap.le
    · intro y
      change ‖Rlambda y‖ ≤ (c - |lambda|)⁻¹ * ‖y‖
      calc
        ‖Rlambda y‖ ≤ ‖Rlambda‖ * ‖y‖ := Rlambda.le_opNorm y
        _ ≤ (c - |lambda|)⁻¹ * ‖y‖ :=
          mul_le_mul_of_nonneg_right hRnorm (norm_nonneg y)

local instance osBoundaryExcitationLogGeneratorResolventNormSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorResolventNormSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorResolventNormSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorResolventNormSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorResolventNormSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorResolventNormSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorResolventNormSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorResolventNormPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

local instance osBoundaryExcitationLogGeneratorResolventNormPairHilbertSectorRealNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) := by
  infer_instance

local instance osBoundaryExcitationLogGeneratorResolventNormSpectralSupportComplete
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

/-- Explicit native real normed-space structure on the completed transfer support. -/
@[reducible] noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRealNormedSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := {
  norm_smul_le := by
    intro c x
    change
      ‖c • (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta)‖ ≤
        ‖c‖ * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)‖
    exact norm_smul_le c
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) }

/-- Inside the completed support logarithmic Hamiltonian gap, the actual-domain
resolvent exists and its ambient realization satisfies
`‖(Hsupp - λI)⁻¹‖ ≤ (2r - |λ|)⁻¹`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_exists_ambientResolvent_norm_le_two_decayRate_sub_abs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let A :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta
    letI :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRealNormedSpace
        H N hN beta hbeta
    lambda ∈ realLinearPMapRealResolventSet A ∧
      ∃ Blambda :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta →L[ℝ]
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta,
        (∀ x : A.domain,
          Blambda (realLinearPMapDomainShift A lambda x) = (x : _)) ∧
        (∀ y, ∃ x : A.domain,
          realLinearPMapDomainShift A lambda x = y ∧ Blambda y = (x : _)) ∧
        ‖Blambda‖ ≤
          (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta - |lambda|)⁻¹ := by
  dsimp only
  let hSupportRealNormedSpace : NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRealNormedSpace
      H N hN beta hbeta
  exact
    @realLinearPMap_exists_ambientResolvent_norm_le_of_abs_lt_norm_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
      _ hSupportRealNormedSpace _
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

end

end MathlibAnalytic
end MGAP4D
