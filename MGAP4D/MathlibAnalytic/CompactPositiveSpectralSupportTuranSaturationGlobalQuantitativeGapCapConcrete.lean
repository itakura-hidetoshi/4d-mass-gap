import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTuranSaturationDerivativeRatioGapCapConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportTuranSaturationGlobalSpectralInvariantConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

local instance turanGlobalGapCapConcreteSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance turanGlobalGapCapConcreteSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance turanGlobalGapCapConcreteSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance turanGlobalGapCapConcreteSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance turanGlobalGapCapConcreteSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance turanGlobalGapCapConcreteSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance turanGlobalGapCapConcreteSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance turanGlobalGapCapConcretePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- A single local Turán saturation propagates the finite-volume coercive gap
control to every admissible factorial-normalized resolvent derivative ratio.

Writing `c = 2 * finiteVolumeDecayRate`, local saturation at `(n, lambda)`
rigidifies a common reconstructed logarithmic energy.  Hence for every
admissible `(m, mu)`, with ratio `Rm`, one has

`0 < Rm ≤ (c - mu)⁻¹`,
`c ≤ mu + Rm⁻¹`,

and the reconstructed one-step transfer value is positive, bounded by the gap
factor, and strictly below one.  Thus the quantitative mass-gap receipt is
independent of both derivative order and resolvent parameter once the Turán
rigidity locus is reached. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_globalQuantitativeGapCap
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
    let Rm := iteratedDeriv (m + 1) q mu /
      ((m + 1 : ℝ) * iteratedDeriv m q mu)
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    0 < Rm ∧
      Rm ≤ (c - mu)⁻¹ ∧
      c ≤ mu + Rm⁻¹ ∧
      0 < Real.exp (-(mu + Rm⁻¹)) ∧
      Real.exp (-(mu + Rm⁻¹)) ≤ Real.exp (-c) ∧
      Real.exp (-(mu + Rm⁻¹)) < 1 := by
  dsimp only at hsaturation ⊢
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let Rn := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let Rm := iteratedDeriv (m + 1) q mu /
    ((m + 1 : ℝ) * iteratedDeriv m q mu)
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  have hglobal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_globalSpectralInvariant
      H N hN beta hbeta v hv n m lambda mu hlambda hmu hsaturation
  dsimp only at hglobal
  rcases hglobal with ⟨_, _, henergy, _, _⟩
  have hquant :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_turanSaturation_quantitativeSpectralGap
      H N hN beta hbeta v hv n lambda hlambda hsaturation
  dsimp only at hquant
  rcases hquant with ⟨_, hcRn, _, hExpUpperN, hExpLtOneN⟩
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
      H N hN beta hbeta v hv m mu hmu
  have hm1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
      H N hN beta hbeta v hv (m + 1) mu hmu
  have hRmPos : 0 < Rm := by
    dsimp [Rm, q]
    positivity
  have hmuC : |mu| < c := by
    simpa [c] using hmu
  have hgapDistancePos : 0 < c - mu := by
    have hmuLtC : mu < c :=
      lt_of_le_of_lt (le_abs_self mu) hmuC
    linarith
  have hcRm : c ≤ mu + Rm⁻¹ := by
    calc
      c ≤ lambda + Rn⁻¹ := hcRn
      _ = mu + Rm⁻¹ := henergy
  have hgapDistance_le_invRm : c - mu ≤ Rm⁻¹ := by
    linarith
  have hmul : (c - mu) * Rm ≤ 1 := by
    have h : c - mu ≤ 1 / Rm := by
      simpa [one_div] using hgapDistance_le_invRm
    exact (le_div_iff₀ hRmPos).mp h
  have hRmUpperDiv : Rm ≤ 1 / (c - mu) := by
    apply (le_div_iff₀ hgapDistancePos).2
    simpa [mul_comm] using hmul
  have hRmUpper : Rm ≤ (c - mu)⁻¹ := by
    simpa [one_div] using hRmUpperDiv
  have hExpPosM : 0 < Real.exp (-(mu + Rm⁻¹)) := Real.exp_pos _
  have hExpUpperM :
      Real.exp (-(mu + Rm⁻¹)) ≤ Real.exp (-c) := by
    calc
      Real.exp (-(mu + Rm⁻¹)) = Real.exp (-(lambda + Rn⁻¹)) := by
        rw [henergy]
      _ ≤ Real.exp (-c) := hExpUpperN
  have hExpLtOneM : Real.exp (-(mu + Rm⁻¹)) < 1 := by
    calc
      Real.exp (-(mu + Rm⁻¹)) = Real.exp (-(lambda + Rn⁻¹)) := by
        rw [henergy]
      _ < 1 := hExpLtOneN
  exact ⟨hRmPos, hRmUpper, hcRm, hExpPosM, hExpUpperM, hExpLtOneM⟩

end

end MathlibAnalytic
end MGAP4D
