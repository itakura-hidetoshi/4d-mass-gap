import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantWeakStarState
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticApproximationFamily
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Reflection data on the physical gauge-invariant observable algebra.

The positive-time observables form a real subalgebra.  Time reflection is an
involutive real-algebra endomorphism of the full gauge-invariant algebra. -/
structure PhysicalYangMillsGaugeInvariantOSReflectionData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) where
  positiveTimeSubalgebra :
    Subalgebra ℝ (physicalYangMillsGaugeInvariantObservableSubalgebra S)
  reflection :
    physicalYangMillsGaugeInvariantObservableSubalgebra S →ₐ[ℝ]
      physicalYangMillsGaugeInvariantObservableSubalgebra S
  reflection_involutive : Function.Involutive reflection

/-- The real Osterwalder--Schrader quadratic observable `Theta(F) * F`. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (F : D.positiveTimeSubalgebra) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  D.reflection (F : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
    (F : physicalYangMillsGaugeInvariantObservableSubalgebra S)

/-- Reflection positivity of a weak-star state on the physical observable
algebra. -/
def PhysicalYangMillsGaugeInvariantOSReflectionData.WeakStarReflectionPositive
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ (physicalYangMillsGaugeInvariantObservableSubalgebra S)) :
    Prop :=
  ∀ F : D.positiveTimeSubalgebra, 0 ≤ omega (D.quadraticObservable F)

/-- Reflection positivity is sequentially closed for the weak-star topology. -/
theorem physical_yang_mills_weakStarReflectionPositive_of_tendsto
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : ℕ → WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (omegaLimit : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (homega : Tendsto omega atTop (nhds omegaLimit))
    (hpositive : ∀ n, D.WeakStarReflectionPositive (omega n)) :
    D.WeakStarReflectionPositive omegaLimit := by
  intro F
  have hEval :
      Tendsto
        (fun n : ℕ => omega n (D.quadraticObservable F))
        atTop
        (nhds (omegaLimit (D.quadraticObservable F))) :=
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp homega)
      (D.quadraticObservable F)
  exact isClosed_Ici.mem_of_tendsto hEval
    (.of_forall fun n => hpositive n F)

/-- If every embedded-lattice physical state is reflection positive, weak-star
convergence transfers reflection positivity to the continuum physical state. -/
theorem physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (hfinite : ∀ n,
      D.WeakStarReflectionPositive
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  exact physical_yang_mills_weakStarReflectionPositive_of_tendsto
    D
    (fun n : ℕ => physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
    (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
    (physical_yang_mills_gaugeInvariantWeakStarState_converges S)
    hfinite

/-- Model-specific bridge from the automatic finite Wilson OS family to the
physical weak-star state sequence.

The sole analytic identification required here is that evaluation of the
physical lattice state on `Theta(F) * F` equals the corresponding finite Wilson
reflection form.  Finite nonnegativity itself is theorem-generated from the
existing Gram/character certificates. -/
structure PhysicalYangMillsFiniteWilsonOSWeakStarBridge
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S) where
  scale : ℕ → W.index
  finiteObservable :
    (n : ℕ) → D.positiveTimeSubalgebra →
      (W.reflectionData (scale n)).PositiveConfiguration → ℝ
  reflectionForm_eq_stateEvaluation :
    ∀ (n : ℕ) (F : D.positiveTimeSubalgebra),
      physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
          (D.quadraticObservable F) =
        (W.reflectionData (scale n)).wilsonReflectionForm
          (finiteObservable n F)

/-- The finite Wilson Gram certificates imply reflection positivity of every
physical approximating state once the state-evaluation bridge is supplied. -/
theorem physical_yang_mills_finiteWilson_bridge_approximating_reflectionPositive
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (B : PhysicalYangMillsFiniteWilsonOSWeakStarBridge W S D)
    (n : ℕ) :
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  intro F
  rw [B.reflectionForm_eq_stateEvaluation n F]
  exact finite_wilson_os_automatic_family_actualReflectionPositive W
    (B.scale n) (B.finiteObservable n F)

/-- Automatic finite Wilson reflection positivity plus the bridge to the
physical lattice states yields continuum reflection positivity. -/
theorem physical_yang_mills_finiteWilson_bridge_continuum_reflectionPositive
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (B : PhysicalYangMillsFiniteWilsonOSWeakStarBridge W S D) :
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  apply physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
    S D
  intro n
  exact physical_yang_mills_finiteWilson_bridge_approximating_reflectionPositive
    W S D B n

end

end MathlibAnalytic
end MGAP4D
