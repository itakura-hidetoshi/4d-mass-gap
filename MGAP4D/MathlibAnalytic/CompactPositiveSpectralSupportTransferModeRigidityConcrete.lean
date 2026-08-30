import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorTransferEigenmode
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventMixedStrictnessClassificationConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance transferModeRigidityConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance transferModeRigidityConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance transferModeRigidityConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance transferModeRigidityConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance transferModeRigidityConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance transferModeRigidityConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance transferModeRigidityConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance transferModeRigidityConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A nonzero physical state on the one-step strictly-positive spectral support
is a single transfer mode when the bounded support restriction of the physical
one-step transfer acts by one strictly-positive scalar. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Prop := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  exact ∃ tau : ℝ, 0 < tau ∧
    realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric v = tau • v

/-- Turán equality for consecutive factorial-normalized derivative ratios is
exactly one-step physical transfer spectral purity.  The proof goes directly
through the explicit actual-domain eigenmode proposition and the generic
support transfer bridge, avoiding the private packaging used by the older
log-generator-language theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_transferMode
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
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
        H N hN beta hbeta v := by
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
      c * ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
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
  have hDomain :=
    realLinearPMapAmbientResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_domain_eigenmode
      A c hc hNorm hKer hSurj hSelfNative hQuad v hv n lambda
      (by simpa [c] using hlambda)
  have hTransfer :=
    realHilbertCompactPositiveZeroSupportLogGenerator_domain_eigenmode_iff_transfer_eigenmode
      T hCompact hPositive v hv
  rw [hGenerator] at hTransfer
  have hiff := hDomain.trans hTransfer
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode,
    A, c, T, hPositive] using hiff

/-- On the concrete physical one-step support, a genuine actual-domain mode of
`-log T` is exactly a strictly-positive spectral mode of the bounded one-step
transfer.  The comparison is made through the common Turán-equality
characterization, so no private helper declaration needs to be unfolded. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_transferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
        H N hN beta hbeta v := by
  have hzero :
      |(0 : ℝ)| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta := by
    simpa using
      (mul_pos (show (0 : ℝ) < 2 by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
          H N hN beta hbeta))
  have hlog :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_logGeneratorMode
      H N hN beta hbeta v hv 0 0 hzero
  have htransfer :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_transferMode
      H N hN beta hbeta v hv 0 0 hzero
  exact hlog.symm.trans htransfer

/-- Strict growth from derivative order `n` to `n+1` occurs exactly when the
physical state is not spectrally pure for the one-step transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_transferMode
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
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_logGeneratorMode
      H N hN beta hbeta v hv n lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_transferMode
      H N hN beta hbeta v hv
  exact hbase.trans (not_congr hbridge)

/-- Strict monotonicity in derivative order is equivalent to failure of one-step
physical transfer spectral purity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_transferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    StrictMono (fun n : ℕ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
      H N hN beta hbeta v hv lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_transferMode
      H N hN beta hbeta v hv
  exact hbase.trans (not_congr hbridge)

/-- Complete mixed strictness classification in transfer language.  Under weak
increase in derivative order and resolvent parameter, strictness occurs exactly
when the parameter increases strictly, or the derivative order increases
strictly while the physical state is not a single one-step transfer mode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_transferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ}
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hmu :
      |mu| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hlm : lambda ≤ mu) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (m + 1) q mu /
        ((m + 1 : ℝ) * iteratedDeriv m q mu) ↔
      lambda < mu ∨
        (n < m ∧
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
            H N hN beta hbeta v) := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_logGeneratorMode
      H N hN beta hbeta v hv hnm hlambda hmu hlm
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_transferMode
      H N hN beta hbeta v hv
  constructor
  · intro hlt
    rcases hbase.mp hlt with hlstrict | ⟨hnmStrict, hnot⟩
    · exact Or.inl hlstrict
    · exact Or.inr ⟨hnmStrict, (not_congr hbridge).mp hnot⟩
  · intro hcase
    apply hbase.mpr
    rcases hcase with hlstrict | ⟨hnmStrict, hnot⟩
    · exact Or.inl hlstrict
    · exact Or.inr ⟨hnmStrict, (not_congr hbridge).mpr hnot⟩

end

end MathlibAnalytic
end MGAP4D
