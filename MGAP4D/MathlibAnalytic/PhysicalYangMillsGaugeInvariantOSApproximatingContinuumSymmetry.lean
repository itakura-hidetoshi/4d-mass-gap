import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

def physicalYangMillsPositiveTimeToSubmodule
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) :
    D.positiveTimeSubalgebra.toSubmodule :=
  ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩

theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F G : D.positiveTimeSubalgebra.toSubmodule) :
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

theorem continuum_reflectionTimeTranslationExchange
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n)) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      C.toContinuumPositiveTimeObservableContractionSemigroup := by
  intro t F G
  let Pinf :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  let Fpos := Pinf.positiveTimeElement F
  let Gpos := Pinf.positiveTimeElement G
  let Ft : D.positiveTimeSubalgebra.toSubmodule :=
    physicalYangMillsPositiveTimeToSubmodule D (C.translate t Fpos)
  let Gt : D.positiveTimeSubalgebra.toSubmodule :=
    physicalYangMillsPositiveTimeToSubmodule D (C.translate t Gpos)
  let Fs : D.positiveTimeSubalgebra.toSubmodule :=
    physicalYangMillsPositiveTimeToSubmodule D Fpos
  let Gs : D.positiveTimeSubalgebra.toSubmodule :=
    physicalYangMillsPositiveTimeToSubmodule D Gpos
  have hleft :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
      S D Ft Gs
  have hright :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
      S D Fs Gt
  have hfunctions :
      (fun n : ℕ =>
        D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          Ft Gs) =
        fun n : ℕ =>
          D.osBilinForm
            (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
            Fs Gt := by
    funext n
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    have h := hExchange n t
      (Pn.carrierOfPositiveTime Fpos)
      (Pn.carrierOfPositiveTime Gpos)
    simp only [(C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation_carrierOfPositiveTime] at h
    change D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        Ft Gs =
      D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        Fs Gt at h
    exact h
  rw [hfunctions] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  change D.osBilinForm Pinf.omega
      (Pinf.toPositiveTime
        (C.toContinuumPositiveTimeObservableContractionSemigroup.carrierTranslation t F))
      (Pinf.toPositiveTime G) =
    D.osBilinForm Pinf.omega
      (Pinf.toPositiveTime F)
      (Pinf.toPositiveTime
        (C.toContinuumPositiveTimeObservableContractionSemigroup.carrierTranslation t G))
  simpa only [Pinf,
    C.toContinuumPositiveTimeObservableContractionSemigroup.carrierTranslation_apply,
    Fpos, Gpos, Ft, Gt, Fs, Gs,
    physicalYangMillsPositiveTimeToSubmodule] using hlimit

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
