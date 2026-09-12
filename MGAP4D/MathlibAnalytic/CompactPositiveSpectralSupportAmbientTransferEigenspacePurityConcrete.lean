import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportAmbientTransferModeRigidityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- For a bounded real-linear operator, a positive scalar eigen-equation is
exactly membership in a positive Mathlib eigenspace.  This is the intrinsic,
coordinate-free form of the ambient eigenmode statement. -/
theorem continuousLinearMap_positive_eigenmode_iff_mem_positive_eigenspace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (v : E) :
    (∃ tau : ℝ, 0 < tau ∧ T v = tau • v) ↔
      ∃ tau : ℝ, 0 < tau ∧ v ∈ eigenspace (T : Module.End ℝ E) tau := by
  constructor
  · rintro ⟨tau, htau, hmode⟩
    refine ⟨tau, htau, ?_⟩
    rw [mem_eigenspace_iff]
    exact hmode
  · rintro ⟨tau, htau, hmem⟩
    refine ⟨tau, htau, ?_⟩
    exact mem_eigenspace_iff.mp hmem

local instance ambientTransferEigenspacePurityConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance ambientTransferEigenspacePurityConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance ambientTransferEigenspacePurityConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance ambientTransferEigenspacePurityConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance ambientTransferEigenspacePurityConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance ambientTransferEigenspacePurityConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance ambientTransferEigenspacePurityConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance ambientTransferEigenspacePurityConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A one-step physical support state is spectrally pure in intrinsic Mathlib
language when its ambient representative lies in one strictly-positive
`eigenspace` of the actual bounded physical transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Prop :=
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  ∃ tau : ℝ, 0 < tau ∧ (v : E) ∈ eigenspace (T : Module.End ℝ E) tau

/-- The ambient eigen-equation formulation is exactly intrinsic membership in
one strictly-positive eigenspace of the actual one-step physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  have hiff :=
    continuousLinearMap_positive_eigenmode_iff_mem_positive_eigenspace
      T (v : E)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferMode,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode,
    E, T] using hiff

/-- A genuine actual-domain logarithmic-generator mode is exactly intrinsic
strictly-positive eigenspace purity for the ambient one-step physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_ambientTransferEigenspaceMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_ambientTransferMode
    H N hN beta hbeta v hv).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
      H N hN beta hbeta v)

/-- Turán equality is exactly intrinsic positive eigenspace purity of the
actual ambient one-step physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_ambientTransferEigenspaceMode
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
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v := by
  dsimp only
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_ambientTransferMode
      H N hN beta hbeta v hv n lambda hlambda).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
        H N hN beta hbeta v)

/-- Adjacent derivative-ratio strictness occurs exactly when the physical state
is not contained in a single positive eigenspace of the ambient transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_ambientTransferEigenspaceMode
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_ambientTransferMode
      H N hN beta hbeta v hv n lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
      H N hN beta hbeta v
  exact hbase.trans (not_congr hbridge)

/-- Strict monotonicity in derivative order is exactly failure of intrinsic
positive eigenspace purity for the ambient one-step transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_ambientTransferEigenspaceMode
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_ambientTransferMode
      H N hN beta hbeta v hv lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
      H N hN beta hbeta v
  exact hbase.trans (not_congr hbridge)

/-- Complete mixed strictness classification in intrinsic ambient eigenspace
language. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_ambientTransferEigenspaceMode
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
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
            H N hN beta hbeta v) := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_ambientTransferMode
      H N hN beta hbeta v hv hnm hlambda hmu hlm
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferMode_iff_ambientTransferEigenspaceMode
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
