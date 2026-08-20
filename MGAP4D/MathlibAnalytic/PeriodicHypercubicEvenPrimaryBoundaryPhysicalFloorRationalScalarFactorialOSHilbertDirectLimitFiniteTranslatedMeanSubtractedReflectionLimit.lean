import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteMeanStationarityBridge
import Mathlib.Tactic

/-!
# Translated-mean-subtracted finite Wilson reflection forms

The preceding two same-root layers establish complementary facts for literal bounded-continuous
fixed-slot cylinders:

* the actual finite Wilson mean-subtracted reflection forms
  `Q_n(τ_h F) - (E_n F)^2` converge to the centered completed-direct-limit OS correlation; and
* on the selected factorial Wilson tail, finite temporal stationarity gives the exact identity
  `E_n[τ_h F] = E_n[F]`.

This file packages the quantitatively natural finite sequence

`Q_n(τ_h F) - (E_n[τ_h F])^2`

as a named same-root object and proves directly that it converges to the centered Hilbert
correlation.  The proof is only eventual equality plus the already-proved weak-limit theorem.

This is the finite sequence on which a future model-derived scale-uniform Euclidean-time decay
estimate can be stated without changing centering conventions between finite and Hilbert levels.
No decay estimate, variance floor, non-collapse, positive mass, spectral gap, old-carrier
identification, or heat-bath/physical-time identification is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory UniformSpace
open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The actual finite Wilson translated reflection form with the translated literal cylinder's
own actual finite Wilson mean subtracted.

Unlike the earlier conservative wrapper, the subtraction here is written at the translated slot
sector itself.  Factorial finite stationarity proves eventual equality of the two wrappers. -/
noncomputable def fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  ((P.fixedSlotDataOfIndex
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
    ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n : Measure (ℚ → ℝ)) -
    ((P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierFiniteMean
      ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F) n) ^ 2

/-- On the selected factorial Wilson tail, the conservative #1908 finite wrapper and the
translated-mean wrapper are exactly equal term by term. -/
theorem fixedSlotCarrierFiniteMeanSubtractedReflectionForm_eventuallyEq_translatedMeanSubtracted
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    (fun n => P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm J h hh F n) =ᶠ[atTop]
      (fun n => P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm J h hh F n) := by
  simpa [fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm] using
    P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm_eventually_eq_translatedMeanSubtracted
      J h hh F

/-- Main finite-to-Hilbert receipt for the quantitatively natural centered sequence:

`Q_n(τ_h F) - (E_n[τ_h F])^2`

converges exactly to

`⟪center(x_F), T_{2h} center(x_F)⟫`.

No positive lower bound or decay rate is used. -/
theorem fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_tendsto_centeredCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n => P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm J h hh F n)
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)))) := by
  exact
    (P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm_tendsto_centeredCorrelation
      J h hh F).congr'
      (P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm_eventuallyEq_translatedMeanSubtracted
        J h hh F)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
