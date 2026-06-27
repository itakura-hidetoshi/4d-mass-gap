import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- For fixed positive-time observables, the finite Wilson OS bilinear forms
converge to the continuum OS bilinear form. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F G : D.positiveTimeSubalgebra) :
    Tendsto
      (fun n : ℕ =>
        D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          F G)
      atTop
      (nhds
        (D.osBilinForm
          (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
          F G)) := by
  have hEval :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp
      (physical_yang_mills_gaugeInvariantWeakStarState_converges S))
      (D.reflection
          (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
        (G : physicalYangMillsGaugeInvariantObservableSubalgebra S))
  simpa only [D.osBilinForm_apply] using hEval

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Reflection/time-translation exchange for every finite Wilson OS state passes
to the continuum Wilson OS state. -/
theorem continuum_reflectionTimeTranslationExchange
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n)) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      C.toContinuumPositiveTimeObservableContractionSemigroup := by
  intro t F G
  let P∞ :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  let Fpos := P∞.positiveTimeElement F
  let Gpos := P∞.positiveTimeElement G
  have hleft :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
      S D (C.translate t Fpos) Gpos
  have hright :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
      S D Fpos (C.translate t Gpos)
  have hfunctions :
      (fun n : ℕ =>
        D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          (C.translate t Fpos) Gpos) =
        fun n : ℕ =>
          D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
            Fpos (C.translate t Gpos) := by
    funext n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    have h := hExchange n t
      (Pn.carrierOfPositiveTime Fpos)
      (Pn.carrierOfPositiveTime Gpos)
    simpa only [Pn.toPositiveTime_carrierOfPositiveTime,
      (C.toPositiveTimeObservableContractionSemigroup n)
        .carrierTranslation_carrierOfPositiveTime] using h
  rw [hfunctions] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  simpa only [Fpos, Gpos,
    P∞.translateCarrierByPositiveTimeAlgHom_apply,
    P∞.carrierOfPositiveTime_positiveTimeElement,
    P∞.toPositiveTime_carrierOfPositiveTime] using hlimit

/-- Consequently the completed continuum transfer semigroup is symmetric for
the physical real inner product. -/
theorem continuumPhysicalSemigroup_isInnerSymmetric
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n)) :
    C.continuumPhysicalSemigroup.IsInnerSymmetric := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange.toPhysicalSemigroup_isInnerSymmetric
      (C.continuum_reflectionTimeTranslationExchange hExchange)

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily

end MathlibAnalytic
end MGAP4D

end
