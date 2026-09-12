import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportAmbientTransferUniqueEigenvalueRigidityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance exactSpectralDictionaryConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance exactSpectralDictionaryConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance exactSpectralDictionaryConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance exactSpectralDictionaryConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance exactSpectralDictionaryConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance exactSpectralDictionaryConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance exactSpectralDictionaryConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance exactSpectralDictionaryConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Exact physical transfer/generator spectral dictionary on the strictly-positive
one-step support.  There is a unique positive ambient transfer eigenvalue `tau`,
and for that `tau` a unique logarithmic-generator energy `rho`; they obey both
`tau = exp (-rho)` and `rho = -log tau`, with a genuine witness in the maximal
domain of the original partially defined support logarithmic generator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Prop := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  exact ∃! tau : ℝ,
    ∃! rho : ℝ,
      0 < tau ∧
      tau = Real.exp (-rho) ∧
      rho = -Real.log tau ∧
      T (v : E) = tau • (v : E) ∧
      ∃ x : A.domain,
        (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) = v ∧
        A x = rho • v

/-- The previously established unique positive ambient transfer eigenvalue is
exactly a unique transfer/generator spectral pair with the exponential/logarithm
relations and a genuine logarithmic-generator domain witness. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
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
  have hGenerator :
      realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive = A := by
    dsimp only [T, A]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    rfl
  let P : ℝ → ℝ → Prop := fun tau rho =>
    0 < tau ∧
    tau = Real.exp (-rho) ∧
    rho = -Real.log tau ∧
    T (v : E) = tau • (v : E) ∧
    ∃ x : A.domain,
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) = v ∧
      A x = rho • v
  have hBuild : ∀ tau : ℝ,
      0 < tau ∧ (v : E) ∈ eigenspace (T : Module.End ℝ E) tau →
        ∃! rho : ℝ, P tau rho := by
    intro tau htau
    have hAmbient : T (v : E) = tau • (v : E) :=
      mem_eigenspace_iff.mp htau.2
    have hRestriction :
        realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric v =
          tau • v :=
      (realHilbertZeroEigenspaceSupportRestriction_eigenmode_iff_ambient_eigenmode
        T hPositive.isSymmetric v tau).mpr hAmbient
    have hReverse :=
      realHilbertCompactPositiveZeroSupportLogGenerator_transfer_eigenmode_to_domain_eigenmode
        T hCompact hPositive v hv tau hRestriction
    rw [hGenerator] at hReverse
    rcases hReverse with ⟨_, x, hxv, hAx⟩
    refine ⟨-Real.log tau, ?_, ?_⟩
    · refine ⟨htau.1, ?_, rfl, hAmbient, x, hxv, hAx⟩
      simpa using (Real.exp_log htau.1).symm
    · intro rho hrho
      exact hrho.2.2.1
  change
    (∃! tau : ℝ, 0 < tau ∧ (v : E) ∈ eigenspace (T : Module.End ℝ E) tau) ↔
      ∃! tau : ℝ, ∃! rho : ℝ, P tau rho
  constructor
  · rintro ⟨tau, htau, huniq⟩
    refine ⟨tau, hBuild tau htau, ?_⟩
    intro sigma hsigma
    rcases hsigma with ⟨rho, hrho, _⟩
    apply huniq sigma
    exact ⟨hrho.1, mem_eigenspace_iff.mpr hrho.2.2.2.1⟩
  · rintro ⟨tau, htauPair, huniqPair⟩
    rcases htauPair with ⟨rho, hrho, _⟩
    refine ⟨tau, ⟨hrho.1, mem_eigenspace_iff.mpr hrho.2.2.2.1⟩, ?_⟩
    intro sigma hsigma
    exact huniqPair sigma (hBuild sigma hsigma)

/-- A genuine actual-domain logarithmic-generator mode is equivalent to the
full exact spectral dictionary: a unique positive one-step transfer eigenvalue
and its unique logarithmic energy, related by `exp` and `log`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_uniqueTransferGeneratorSpectralPair
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_uniquePositiveAmbientTransferEigenvalue
    H N hN beta hbeta v hv).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv)

/-- Turán equality is exactly the existence of the unique exact physical
transfer/generator spectral pair. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniqueTransferGeneratorSpectralPair
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
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v := by
  dsimp only
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniquePositiveAmbientTransferEigenvalue
      H N hN beta hbeta v hv n lambda hlambda).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v hv)

/-- Adjacent derivative-ratio strictness occurs exactly when the state fails to
carry the unique exact transfer/generator spectral pair. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_uniqueTransferGeneratorSpectralPair
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_uniquePositiveAmbientTransferEigenvalue
      H N hN beta hbeta v hv n lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv
  rw [hbridge] at hbase
  exact hbase

/-- Strict monotonicity in derivative order is exactly failure of the exact
transfer/generator spectral dictionary. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_uniqueTransferGeneratorSpectralPair
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_uniquePositiveAmbientTransferEigenvalue
      H N hN beta hbeta v hv lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv
  rw [hbridge] at hbase
  exact hbase

/-- Complete mixed strictness classification in the exact spectral-dictionary
language. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_uniqueTransferGeneratorSpectralPair
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
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
            H N hN beta hbeta v) := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_uniquePositiveAmbientTransferEigenvalue
      H N hN beta hbeta v hv hnm hlambda hmu hlm
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_uniquePositiveAmbientTransferEigenvalue_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv
  rw [hbridge] at hbase
  exact hbase

end

end MathlibAnalytic
end MGAP4D
