import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranEquality
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance supportResolventTuranEqualityConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance supportResolventTuranEqualityConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance supportResolventTuranEqualityConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance supportResolventTuranEqualityConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance supportResolventTuranEqualityConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance supportResolventTuranEqualityConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance supportResolventTuranEqualityConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance supportResolventTuranEqualityConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The actual bounded resolvent on the one-step positive physical spectral
support.  The public return type is written through the native zero-eigenspace
support rather than the long physical alias, so Hilbert-space instance search
stays on the already established subtype structure. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventFamily
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (lambda : ℝ) :
    let T :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1
    realHilbertZeroEigenspaceSupport T →L[ℝ] realHilbertZeroEigenspaceSupport T := by
  dsimp only
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  change realHilbertZeroEigenspaceSupport T →L[ℝ] realHilbertZeroEigenspaceSupport T
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) := by
    exact (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let A : realHilbertZeroEigenspaceSupport T →ₗ.[ℝ]
      realHilbertZeroEigenspaceSupport T :=
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
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖A x‖ := by
    intro x
    simpa [A, c, T] using
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
  exact
    realLinearPMapAmbientResolventFamily_of_norm_lower_bound
      A c hc hNorm hKer hSurj lambda

/-- On the actual positive physical spectral support, equality of consecutive
factorial-normalized derivative ratios is equivalent to the state occupying a
single spectral mode of the bounded support resolvent.  This is the exact
rigidity alternative behind the non-strict degree order. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_eigenmode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let F :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventFamily
        H N hN beta hbeta lambda
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      ∃ r : ℝ, F v = r • v := by
  dsimp only
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  letI : CompleteSpace (realHilbertZeroEigenspaceSupport T) := by
    exact (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  let A : realHilbertZeroEigenspaceSupport T →ₗ.[ℝ]
      realHilbertZeroEigenspaceSupport T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let u : realHilbertZeroEigenspaceSupport T := v
  have hu : u ≠ 0 := by
    simpa [u] using hv
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hc : 0 < c := by
    exact mul_pos (by norm_num)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta)
  have hNorm : ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ≤ ‖A x‖ := by
    intro x
    simpa [A, c, T] using
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
  have hQuad : ∀ x : A.domain,
      c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
        inner ℝ (A x) (x : realHilbertZeroEigenspaceSupport T) := by
    intro x
    simpa [A, c, T] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x)
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
  have hiff :=
    realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_eigenmode
      A c hc hNorm hKer hSurj hSelfNative hQuad u hu n lambda
      (by simpa [c] using hlambda)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventFamily,
    A, c, T, u] using hiff

end

end MathlibAnalytic
end MGAP4D
