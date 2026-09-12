import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTuranSaturationExactSpectralReconstructionConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance turanGlobalInvariantConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance turanGlobalInvariantConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance turanGlobalInvariantConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance turanGlobalInvariantConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance turanGlobalInvariantConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance turanGlobalInvariantConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance turanGlobalInvariantConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance turanGlobalInvariantConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- One local Turán saturation rigidifies the entire physical normalized
resolvent derivative-ratio family.  Once `R_n(lambda) = R_{n+1}(lambda)` at one
admissible point, every admissible order/parameter pair reconstructs the same
logarithmic-generator energy, and hence the same positive one-step transfer
spectral value.

In particular, if `Rk(s)` denotes the factorial-normalized consecutive ratio,
then
`lambda + R_n(lambda)⁻¹ = mu + R_m(mu)⁻¹`
and
`R_m(mu) = ((lambda + R_n(lambda)⁻¹) - mu)⁻¹`.
Thus the reconstructed energy is independent of both derivative order and
resolvent parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_globalSpectralInvariant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (n m : ℕ) (lambda mu : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hmu :
      |mu| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hsaturation :
      let q :=
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v
      iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
        iteratedDeriv (n + 2) q lambda /
          ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    let Rn := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let Rm := iteratedDeriv (m + 1) q mu /
      ((m + 1 : ℝ) * iteratedDeriv m q mu)
    Rn ≠ 0 ∧
      Rm ≠ 0 ∧
      lambda + Rn⁻¹ = mu + Rm⁻¹ ∧
      Rm = ((lambda + Rn⁻¹) - mu)⁻¹ ∧
      Real.exp (-(lambda + Rn⁻¹)) = Real.exp (-(mu + Rm⁻¹)) := by
  dsimp only at hsaturation ⊢
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta
  let T : E →L[ℝ] E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let Rn := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let Rm := iteratedDeriv (m + 1) q mu /
    ((m + 1 : ℝ) * iteratedDeriv m q mu)
  have hpair :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportHasUniqueTransferGeneratorSpectralPair
        H N hN beta hbeta v :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_uniqueTransferGeneratorSpectralPair
      H N hN beta hbeta v hv n lambda hlambda).mp hsaturation
  change
    (∃! tau : ℝ,
      ∃! rho : ℝ,
        0 < tau ∧
        tau = Real.exp (-rho) ∧
        rho = -Real.log tau ∧
        T (v : E) = tau • (v : E) ∧
        ∃ x : A.domain,
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta) = v ∧
          A x = rho • v) at hpair
  rcases hpair with ⟨tau, htauPair, _⟩
  rcases htauPair with ⟨rho, hrho, _⟩
  rcases hrho with ⟨_, _, _, _, x, hxv, hAx⟩
  have hRn : Rn = (rho - lambda)⁻¹ := by
    simpa [Rn, q, A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorEigenmode
        H N hN beta hbeta v hv rho x hxv hAx n lambda hlambda)
  have hRm : Rm = (rho - mu)⁻¹ := by
    simpa [Rm, q, A] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorEigenmode
        H N hN beta hbeta v hv rho x hxv hAx m mu hmu)
  have hRnPos : 0 < Rn := by
    have hn :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv n lambda hlambda
    have hn1 :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda hlambda
    dsimp [Rn, q]
    positivity
  have hRmPos : 0 < Rm := by
    have hm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv m mu hmu
    have hm1 :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (m + 1) mu hmu
    dsimp [Rm, q]
    positivity
  have hRn0 : Rn ≠ 0 := ne_of_gt hRnPos
  have hRm0 : Rm ≠ 0 := ne_of_gt hRmPos
  have hreconstructN : rho = lambda + Rn⁻¹ := by
    rw [hRn]
    simp
  have hreconstructM : rho = mu + Rm⁻¹ := by
    rw [hRm]
    simp
  have henergy : lambda + Rn⁻¹ = mu + Rm⁻¹ :=
    hreconstructN.symm.trans hreconstructM
  refine ⟨hRn0, hRm0, henergy, ?_, ?_⟩
  · calc
      Rm = (rho - mu)⁻¹ := hRm
      _ = ((lambda + Rn⁻¹) - mu)⁻¹ := by rw [hreconstructN]
  · rw [henergy]

end

end MathlibAnalytic
end MGAP4D
