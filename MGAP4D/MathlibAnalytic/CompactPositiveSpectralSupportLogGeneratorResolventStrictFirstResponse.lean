import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictQuadraticPositivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- The coercively generated ambient resolvent has trivial kernel throughout
its symmetric gap.  This is a direct consequence of the actual-domain
preimage receipt and does not require the forward operator to be bounded. -/
theorem realLinearPMapAmbientResolventFamily_eq_zero_iff
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c)
    (y : E) :
    realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda y = 0 ↔ y = 0 := by
  constructor
  · intro hFy
    rcases realLinearPMapAmbientResolventFamily_exists_domain_preimage
        A c hc hNorm hKer hSurj lambda hlambda y with
      ⟨x, hxy, hFx⟩
    have hxcoe : (x : E) = 0 := by
      rw [← hFx]
      exact hFy
    have hx : x = 0 := by
      apply Subtype.ext
      exact hxcoe
    rw [← hxy, hx]
    simp [realLinearPMapDomainShift]
  · intro hy
    rw [hy]
    exact map_zero _

/-- Hence every bounded ambient resolvent in the coercive gap is injective. -/
theorem realLinearPMapAmbientResolventFamily_injective
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    Function.Injective
      (realLinearPMapAmbientResolventFamily_of_norm_lower_bound
        A c hc hNorm hKer hSurj lambda) := by
  intro y z hyz
  have hsub :
      realLinearPMapAmbientResolventFamily_of_norm_lower_bound
          A c hc hNorm hKer hSurj lambda (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  have hyz0 : y - z = 0 :=
    (realLinearPMapAmbientResolventFamily_eq_zero_iff
      A c hc hNorm hKer hSurj lambda hlambda (y - z)).mp hsub
  exact sub_eq_zero.mp hyz0

/-- For a self-adjoint coercive forward operator, the first scalar derivative
of every nonzero quadratic resolvent amplitude is strictly positive on the
whole symmetric coercive gap.  In particular the response is locally
strictly increasing everywhere in the gap. -/
theorem realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_one_pos
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →ₗ.[ℝ] E)
    (c : ℝ)
    (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0)
    (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (u : E)
    (hu : u ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| < c) :
    0 < iteratedDeriv 1
      (realLinearPMapAmbientResolventQuadraticAmplitude
        A c hc hNorm hKer hSurj u)
      lambda := by
  let F := realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    A c hc hNorm hKer hSurj
  have hformula :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      A c hc hNorm hKer hSurj u 1 lambda hlambda
  have hFself :=
    realLinearPMapAmbientResolventFamily_isSelfAdjoint_of_isSelfAdjoint
      A c hc hNorm hKer hSurj hSelf lambda hlambda
  have hFsymm : (F lambda).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hFself
  have hFu : F lambda u ≠ 0 := by
    intro hzero
    apply hu
    apply realLinearPMapAmbientResolventFamily_injective
      A c hc hNorm hKer hSurj lambda hlambda
    simpa [F] using hzero
  have hsymm :
      inner ℝ (F lambda (F lambda u)) u =
        inner ℝ (F lambda u) (F lambda u) := by
    exact hFsymm (F lambda u) u
  rw [hformula]
  norm_num
  change 0 < inner ℝ (F lambda (F lambda u)) u
  calc
    0 < inner ℝ (F lambda u) (F lambda u) := by
      rw [real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hFu)
    _ = inner ℝ (F lambda (F lambda u)) u := hsymm.symm

local instance supportResolventFirstResponseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportResolventFirstResponseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportResolventFirstResponseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportResolventFirstResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportResolventFirstResponseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportResolventFirstResponseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportResolventFirstResponseSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportResolventFirstResponsePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Physical strict first-response receipt for the actual one-step support
logarithmic resolvent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_one_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hu : u ≠ 0)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    0 < iteratedDeriv 1
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta u)
      lambda := by
  letI : CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
    change CompleteSpace
      (realHilbertZeroEigenspaceSupport
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1))
    exact
      (realHilbertZeroEigenspaceSupport_isClosed
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1)).completeSpace_coe
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
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
  have hNorm : ∀ x : A.domain,
      c * ‖(x :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ ≤ ‖A x‖ := by
    intro x
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta x)
  have hKer : ∀ x : A.domain, A x = 0 → x = 0 := by
    intro x hx
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta x hx
  have hSurj : Function.Surjective A.toFun := by
    simpa [A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)
  have hGenerator :
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive = A := by
    dsimp only [T, A]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    rfl
  have hSelfNative :=
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      T hCompact hPositive
  rw [hGenerator] at hSelfNative
  have hstrict :=
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_one_pos
      (E := realHilbertZeroEigenspaceSupport T)
      A c hc hNorm hKer hSurj hSelfNative u hu lambda
      (by simpa [c] using hlambda)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    A, c] using hstrict

end

end MathlibAnalytic
end MGAP4D
