import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportAmbientTransferEigenspacePurityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

universe u

/-- A nonzero vector cannot lie in eigenspaces of a bounded real-linear
operator for two distinct eigenvalues. -/
theorem continuousLinearMap_eigenvalue_unique_of_mem_eigenspace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (v : E)
    (hv : v ≠ 0)
    {tau sigma : ℝ}
    (htau : v ∈ eigenspace (T : Module.End ℝ E) tau)
    (hsigma : v ∈ eigenspace (T : Module.End ℝ E) sigma) :
    tau = sigma := by
  apply (smul_left_injective ℝ hv)
  calc
    tau • v = T v := (mem_eigenspace_iff.mp htau).symm
    _ = sigma • v := mem_eigenspace_iff.mp hsigma

/-- For a nonzero vector, existence of a strictly-positive ambient eigenvalue
is automatically existence of a unique such eigenvalue. -/
theorem continuousLinearMap_mem_positive_eigenspace_iff_existsUnique
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (v : E)
    (hv : v ≠ 0) :
    (∃ tau : ℝ, 0 < tau ∧ v ∈ eigenspace (T : Module.End ℝ E) tau) ↔
      ∃! tau : ℝ, 0 < tau ∧ v ∈ eigenspace (T : Module.End ℝ E) tau := by
  constructor
  · rintro ⟨tau, htau, hmem⟩
    refine ⟨tau, ⟨htau, hmem⟩, ?_⟩
    intro sigma hsigma
    exact continuousLinearMap_eigenvalue_unique_of_mem_eigenspace
      T v hv hsigma.2 hmem
  · rintro ⟨tau, htau, _⟩
    exact ⟨tau, htau.1, htau.2⟩

local instance uniqueEigenvalueRigidityConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance uniqueEigenvalueRigidityConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance uniqueEigenvalueRigidityConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance uniqueEigenvalueRigidityConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance uniqueEigenvalueRigidityConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance uniqueEigenvalueRigidityConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance uniqueEigenvalueRigidityConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance uniqueEigenvalueRigidityConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A nonzero one-step physical support state has a unique positive ambient
transfer eigenvalue when there is exactly one strictly-positive `tau` whose
Mathlib eigenspace contains its ambient representative. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) : Prop :=
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  ∃! tau : ℝ, 0 < tau ∧ (v : E) ∈ eigenspace (T : Module.End ℝ E) tau

/-- For a nonzero physical support state, intrinsic positive eigenspace purity
is exactly uniqueness of the positive ambient one-step transfer eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta)
    (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  have hvE : (v : E) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  have hiff :=
    continuousLinearMap_mem_positive_eigenspace_iff_existsUnique T (v : E) hvE
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleAmbientTransferEigenspaceMode,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue,
    E, T] using hiff

/-- A genuine actual-domain logarithmic-generator mode is equivalent to having
a unique positive eigenvalue for the actual ambient one-step physical transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_uniquePositiveAmbientTransferEigenvalue
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_logGeneratorMode_iff_ambientTransferEigenspaceMode
    H N hN beta hbeta v hv).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
      H N hN beta hbeta v hv)

/-- Turán equality is exactly uniqueness of the positive ambient one-step
physical transfer eigenvalue carried by the nonzero support state. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniquePositiveAmbientTransferEigenvalue
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
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v := by
  dsimp only
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_ambientTransferEigenspaceMode
      H N hN beta hbeta v hv n lambda hlambda).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
        H N hN beta hbeta v hv)

/-- Adjacent derivative-ratio strictness occurs exactly when the nonzero
physical support state does not carry a unique positive ambient transfer
eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_uniquePositiveAmbientTransferEigenvalue
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_ambientTransferEigenspaceMode
      H N hN beta hbeta v hv n lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
      H N hN beta hbeta v hv
  exact hbase.trans (not_congr hbridge)

/-- Strict monotonicity in derivative order is exactly failure of unique
positive ambient transfer-eigenvalue purity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_uniquePositiveAmbientTransferEigenvalue
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
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
        H N hN beta hbeta v := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_ambientTransferEigenspaceMode
      H N hN beta hbeta v hv lambda hlambda
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
      H N hN beta hbeta v hv
  exact hbase.trans (not_congr hbridge)

/-- Complete mixed strictness classification in terms of uniqueness of the
positive ambient one-step physical transfer eigenvalue. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_uniquePositiveAmbientTransferEigenvalue
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
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniquePositiveAmbientTransferEigenvalue
            H N hN beta hbeta v) := by
  dsimp only
  have hbase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_ambientTransferEigenspaceMode
      H N hN beta hbeta v hv hnm hlambda hmu hlm
  have hbridge :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_ambientTransferEigenspaceMode_iff_uniquePositiveEigenvalue
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
