import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import Mathlib.Topology.Order.OrderClosed

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- On a positive-time observable, the OS quadratic value is exactly evaluation
of the weak-star state on `Theta(F) * F`. -/
@[simp] theorem osQuadraticValue_carrierOfPositiveTime
    (P : D.OSPreHilbertData) (F : D.positiveTimeSubalgebra) :
    P.osQuadraticValue (P.carrierOfPositiveTime F) =
      P.omega (D.quadraticObservable F) := by
  rw [osQuadraticValue, D.osBilinForm_apply]
  rfl

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- For every fixed positive-time observable, the actual finite Wilson OS
quadratic values converge to the continuum Wilson OS quadratic value. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_osQuadraticValue_tendsto
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (F : D.positiveTimeSubalgebra) :
    Tendsto
      (fun n : ℕ =>
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue
          ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).carrierOfPositiveTime F))
      atTop
      (nhds
        ((physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant).osQuadraticValue
          ((physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant).carrierOfPositiveTime F))) := by
  have hEval :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp
      (physical_yang_mills_gaugeInvariantWeakStarState_converges S))
      (D.quadraticObservable F)
  simpa only [PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.osQuadraticValue_carrierOfPositiveTime]
    using hEval

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

/-- Contractivity for every actual finite Wilson OS state passes to the continuum
OS state by weak-star convergence and closedness of the order relation.

Thus a common observable translation family which is contractive at all finite
scales automatically generates the continuum completed contraction semigroup. -/
noncomputable def toContinuumPositiveTimeObservableContractionSemigroup
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant) where
  translate := C.translate
  translate_zero := C.translate_zero
  translate_add := C.translate_add
  osQuadratic_translate_le := by
    intro t F
    let P∞ :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    let Fpos := P∞.positiveTimeElement F
    have hleft :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_osQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta B hInvariant (C.translate t Fpos)
    have hright :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_osQuadraticValue_tendsto
        S D halfExtent N hN beta hbeta B hInvariant Fpos
    have hfinite : ∀ n : ℕ,
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n).carrierOfPositiveTime
                (C.translate t Fpos)) ≤
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).osQuadraticValue
            ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
              S D halfExtent N hN beta hbeta B hInvariant n).carrierOfPositiveTime
                Fpos) := by
      intro n
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      have h := C.osQuadratic_translate_le n t (Pn.carrierOfPositiveTime Fpos)
      simpa only [Pn.translateCarrierByPositiveTimeAlgHom_apply,
        Pn.positiveTimeElement_carrierOfPositiveTime] using h
    have hlimit := le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall hfinite)
    simpa only [Fpos, P∞.translateCarrierByPositiveTimeAlgHom_apply,
      P∞.carrierOfPositiveTime_positiveTimeElement] using hlimit

/-- The completed continuum physical contraction semigroup generated entirely
from finite Wilson OS contractivity. -/
noncomputable def continuumPhysicalSemigroup
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant) :=
  PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.toPhysicalSemigroup
    C.toContinuumPositiveTimeObservableContractionSemigroup

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily

end MathlibAnalytic
end MGAP4D

end
