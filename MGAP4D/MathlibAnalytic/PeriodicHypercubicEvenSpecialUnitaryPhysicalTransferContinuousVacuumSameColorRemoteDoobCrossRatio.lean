import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorRemoteWeightHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCrossRatioComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumSameColorRemoteDoobCrossRatioSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuousVacuumSameColorRemoteDoobCrossRatioIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumSameColorRemoteDoobCrossRatioCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumSameColorRemoteDoobCrossRatioSecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumSameColorRemoteDoobCrossRatioMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumSameColorRemoteDoobCrossRatioBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The current physical continuous-vacuum Harnack control implies an explicit
four-point multiplicative oscillation bound for the two same-color remote Doob
weight families on their common raw target-link law.

With `R = exp (8 * beta)`, the present estimate is

`wh g₁ * wk g₂ ≤ R² * wk g₁ * wh g₂`.

Thus the presently available model-facing cross-ratio coefficient is
`R² = exp (16 * beta)`.  This theorem deliberately does **not** claim that this
coarse coefficient is sharp, distance-decaying, summable over remote sources,
or sufficient for a volume-independent Dobrushin row sum.  Its role is to
isolate the exact four-point quantity that must be improved by a future
clustering, cancellation, or geometric argument. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_normalForm_weight_crossRatio
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
        H N hN beta hbeta
    let wh := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Omega (C.base.replaceLink
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
    let wk := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      Omega (C.base.replaceLink
        (C.base.replaceLink A
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
    let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
    ∀ g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ,
      wh g₁ * wk g₂ ≤ (R * R) * (wk g₁ * wh g₂) := by
  dsimp only
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullConfigurationWeight
      H N hN beta hbeta
  let wh := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    Omega (C.base.replaceLink
      (C.base.replaceLink A
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) h)
  let wk := fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
    Omega (C.base.replaceLink
      (C.base.replaceLink A
        (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) g)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) k)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  have hNormal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_sameColor_remoteDoob_normalForm_weight_harnack
      H N hN beta hbeta hColor hne A h k
  have hHarnack : ∀ g, wh g ≤ R * wk g ∧ wk g ≤ R * wh g := by
    simpa [C, Omega, wh, wk, R] using hNormal.2.2
  intro g₁ g₂
  calc
    wh g₁ * wk g₂ ≤ (R * wk g₁) * (R * wh g₂) := by
      gcongr
      · exact (hHarnack g₁).1
      · exact (hHarnack g₂).2
    _ = (R * R) * (wk g₁ * wh g₂) := by
      ac_rfl

end

end MathlibAnalytic
end MGAP4D
