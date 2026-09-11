import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTransferModeRigidityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- On an invariant zero-eigenspace support, the restricted eigen-equation is
exactly the ambient eigen-equation after forgetting the support subtype. -/
theorem realHilbertZeroEigenspaceSupportRestriction_eigenmode_iff_ambient_eigenmode
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    (v : realHilbertZeroEigenspaceSupport T)
    (tau : ℝ) :
    realHilbertZeroEigenspaceSupportRestriction T hSymm v = tau • v ↔
      T (v : E) = tau • (v : E) := by
  constructor
  · intro h
    have hcoe := congrArg
      (fun w : realHilbertZeroEigenspaceSupport T => (w : E)) h
    simpa using hcoe
  · intro h
    apply Subtype.ext
    simpa using h

/-- Positive eigenmode existence on the support restriction is equivalent to
positive eigenmode existence for the original bounded operator acting on the
same support vector in the ambient Hilbert space. -/
theorem realHilbertZeroEigenspaceSupportRestriction_positive_eigenmode_iff_ambient_positive_eigenmode
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    (v : realHilbertZeroEigenspaceSupport T) :
    (∃ tau : ℝ, 0 < tau ∧
        realHilbertZeroEigenspaceSupportRestriction T hSymm v = tau • v) ↔
      ∃ tau : ℝ, 0 < tau ∧ T (v : E) = tau • (v : E) := by
  constructor
  · rintro ⟨tau, htau, hmode⟩
    exact ⟨tau, htau,
      (realHilbertZeroEigenspaceSupportRestriction_eigenmode_iff_ambient_eigenmode
        T hSymm v tau).mp hmode⟩
  · rintro ⟨tau, htau, hmode⟩
    exact ⟨tau, htau,
      (realHilbertZeroEigenspaceSupportRestriction_eigenmode_iff_ambient_eigenmode
        T hSymm v tau).mpr hmode⟩

local instance ambientTransferModeRigidityConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance ambientTransferModeRigidityConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance ambientTransferModeRigidityConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance ambientTransferModeRigidityConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance ambientTransferModeRigidityConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance ambientTransferModeRigidityConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance ambientTransferModeRigidityConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance ambientTransferModeRigidityConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A support state is a single ambient physical transfer mode when the actual
one-step physical transfer, before support restriction, acts on its ambient
representative by one strictly-positive scalar. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Prop :=
  ∃ tau : ℝ, 0 < tau ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1
        (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) =
      tau •
        (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)

/-- The support-restriction transfer-mode proposition merged previously is
exactly the ambient one-step physical transfer eigenmode proposition. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  have hiff :=
    realHilbertZeroEigenspaceSupportRestriction_positive_eigenmode_iff_ambient_positive_eigenmode
      T hPositive.isSymmetric v
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleTransferMode,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport,
    T, hPositive] using hiff

/-- A genuine actual-domain logarithmic-generator mode is therefore exactly an
ambient strictly-positive one-step physical transfer eigenmode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_ambientTransferMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_transferMode
    H N hN beta hbeta v hv).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
      H N hN beta hbeta v)

/-- Turán equality is exactly spectral purity for the actual ambient one-step
physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_ambientTransferMode
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
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v := by
  dsimp only
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_transferMode
      H N hN beta hbeta v hv n lambda hlambda).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
        H N hN beta hbeta v)

/-- Adjacent derivative-ratio strictness occurs exactly when the support state
is not a single ambient one-step physical transfer eigenmode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_ambientTransferMode
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_transferMode
      H N hN beta hbeta v hv n lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
      H N hN beta hbeta v
  exact hbase.trans (not_congr hbridge)

/-- Strict monotonicity in derivative order is exactly failure of ambient
one-step physical transfer spectral purity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_ambientTransferMode
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_transferMode
      H N hN beta hbeta v hv lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
      H N hN beta hbeta v
  exact hbase.trans (not_congr hbridge)

/-- Complete mixed strictness classification in the language of the actual
ambient one-step physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_ambientTransferMode
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
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
            H N hN beta hbeta v) := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_transferMode
      H N hN beta hbeta v hv hnm hlambda hmu hlm
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_transferMode_iff_ambientTransferMode
      H N hN beta hbeta v
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
