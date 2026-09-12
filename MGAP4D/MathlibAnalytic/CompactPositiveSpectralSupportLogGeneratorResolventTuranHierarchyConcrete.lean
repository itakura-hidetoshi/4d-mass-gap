import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchy
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- Native zero-eigenspace-support bridge for the factorial-normalized Turán
hierarchy.  Support completeness is fixed before the partially defined
logarithmic generator enters adjoint/typeclass search. -/
private theorem realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_iteratedDeriv_turan
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) [CompleteSpace (realHilbertZeroEigenspaceSupport T)]
    (A : realHilbertZeroEigenspaceSupport T →ₗ.[ℝ] realHilbertZeroEigenspaceSupport T)
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ x : A.domain, c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖A x‖)
    (hKer : ∀ x : A.domain, A x = 0 → x = 0) (hSurj : Function.Surjective A.toFun)
    (hSelf : IsSelfAdjoint A)
    (hQuad : ∀ x : A.domain, c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
      inner ℝ (A x) (x : realHilbertZeroEigenspaceSupport T))
    (v : realHilbertZeroEigenspaceSupport T) (hv : v ≠ 0)
    (n : ℕ) (lambda : ℝ) (hlambda : |lambda| < c) :
    (n + 2 : ℝ) *
        (iteratedDeriv (n + 1)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj v) lambda) ^ 2 ≤
      (n + 1 : ℝ) *
        iteratedDeriv n
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj v) lambda *
        iteratedDeriv (n + 2)
          (realLinearPMapAmbientResolventQuadraticAmplitude A c hc hNorm hKer hSurj v) lambda := by
  exact realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_turan
    A c hc hNorm hKer hSurj hSelf hQuad v hv n lambda hlambda

local instance supportResolventTuranConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportResolventTuranConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportResolventTuranConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportResolventTuranConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportResolventTuranConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportResolventTuranConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportResolventTuranConcreteSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportResolventTuranConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta

local instance supportResolventTuranConcreteSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact
    (realHilbertZeroEigenspaceSupport_isClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)).completeSpace_coe

/-- Physical all-order Turán inequality.  For every nonzero state in the
actual one-step positive spectral support and every parameter in the full
symmetric finite-volume coercive gap, consecutive scalar resolvent responses
obey the factorial-normalized log-convexity inequality. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_turan
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda : |lambda| < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta) :
    let q := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
    (n + 2 : ℝ) * (iteratedDeriv (n + 1) q lambda) ^ 2 ≤
      (n + 1 : ℝ) * iteratedDeriv n q lambda * iteratedDeriv (n + 2) q lambda := by
  dsimp only
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
    (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
    H N hN beta hbeta
  let c := 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hNorm : ∀ x : A.domain,
      c * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ≤ ‖A x‖ := by
    intro x
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta x)
  have hKer : ∀ x : A.domain, A x = 0 → x = 0 := by
    intro x hx
    exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta x hx
  have hSurj : Function.Surjective A.toFun := by
    simpa [A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)
  have hQuad : ∀ x : A.domain,
      c * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ^ 2 ≤
        inner ℝ (A x)
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) := by
    intro x
    simpa [A, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x)
  have hGenerator : realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive = A := by
    dsimp only [T, A]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    rfl
  have hSelfNative := realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
    T hCompact hPositive
  rw [hGenerator] at hSelfNative
  have hturan :=
    realHilbertZeroEigenspaceSupport_resolventQuadraticAmplitude_iteratedDeriv_turan
      T A c hc hNorm hKer hSurj hSelfNative hQuad v hv n lambda
      (by simpa [c] using hlambda)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    A, c] using hturan

end

end MathlibAnalytic
end MGAP4D
