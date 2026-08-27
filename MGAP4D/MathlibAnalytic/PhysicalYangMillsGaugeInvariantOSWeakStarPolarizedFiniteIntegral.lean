import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingFiniteIntegralGap
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osWeakStarPolarizedFiniteIntegralSideLengthNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance osWeakStarPolarizedFiniteIntegralSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osWeakStarPolarizedFiniteIntegralSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osWeakStarPolarizedFiniteIntegralSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osWeakStarPolarizedFiniteIntegralSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osWeakStarPolarizedFiniteIntegralSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real Osterwalder--Schrader polarization on the physical positive-time
observable algebra.

Reflection invariance makes the OS bilinear form symmetric, so Mathlib's
`LinearMap.BilinForm.IsSymm.polarization` recovers every cross matrix
coefficient from the three diagonal quadratic observables `F + G`, `F`, and
`G`.  No additional positivity or finite-volume hypothesis is needed. -/
theorem PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_eq_quadratic_polarization
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (omega : WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra S))
    (hInvariant : D.WeakStarReflectionInvariant omega)
    (F G : D.positiveTimeSubalgebra) :
    let Fm : D.positiveTimeSubalgebra.toSubmodule :=
      ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩
    let Gm : D.positiveTimeSubalgebra.toSubmodule :=
      ⟨(G : physicalYangMillsGaugeInvariantObservableSubalgebra S), G.property⟩
    D.osBilinForm omega Fm Gm =
      (omega (D.quadraticObservable (F + G)) -
          omega (D.quadraticObservable F) -
          omega (D.quadraticObservable G)) / 2 := by
  dsimp only
  let Fm : D.positiveTimeSubalgebra.toSubmodule :=
    ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩
  let Gm : D.positiveTimeSubalgebra.toSubmodule :=
    ⟨(G : physicalYangMillsGaugeInvariantObservableSubalgebra S), G.property⟩
  have hpol :=
    (D.osBilinForm_isSymm omega hInvariant).polarization Fm Gm
  simpa [Fm, Gm,
    PhysicalYangMillsGaugeInvariantOSReflectionData.osBilinForm_apply,
    PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticObservable] using hpol

/-- The finite periodic Wilson cross form obtained by polarizing the three
actual reflected Gibbs integrals associated with `F + G`, `F`, and `G`.

This is deliberately defined only from the existing weak-star pullback bridge;
it does not postulate a new cross-observable pullback. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSFinitePolarizedReflectedIntegral
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
    (n : ℕ)
    (F G : D.positiveTimeSubalgebra) : ℝ :=
  let BFG := B.finiteBridge (F + G)
  let BF := B.finiteBridge F
  let BG := B.finiteBridge G
  ((∫ A,
      periodicHypercubicEvenFullReflectedObservable
        (halfExtent n) (BFG.positiveHalfObservable n) A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).gibbsMeasure) -
    (∫ A,
      periodicHypercubicEvenFullReflectedObservable
        (halfExtent n) (BF.positiveHalfObservable n) A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).gibbsMeasure) -
    (∫ A,
      periodicHypercubicEvenFullReflectedObservable
        (halfExtent n) (BG.positiveHalfObservable n) A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).gibbsMeasure)) / 2

/-- Every cross coefficient of the `n`-th physical approximating OS bilinear
form is exactly a polarization of three actual finite periodic `SU(N)` Wilson
Gibbs reflected integrals.

Thus the existing quadratic weak-star bridge already determines the full
symmetric OS form; no separate model-dependent cross-term bridge is required. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_eq_finitePolarizedReflectedIntegral
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
    (n : ℕ)
    (F G : D.positiveTimeSubalgebra) :
    let Fm : D.positiveTimeSubalgebra.toSubmodule :=
      ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩
    let Gm : D.positiveTimeSubalgebra.toSubmodule :=
      ⟨(G : physicalYangMillsGaugeInvariantObservableSubalgebra S), G.property⟩
    D.osBilinForm
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
        Fm Gm =
      physicalYangMillsEvenPeriodicWilsonOSFinitePolarizedReflectedIntegral
        S D halfExtent N hN beta hbeta B n F G := by
  dsimp only
  let omega := physicalYangMillsApproximatingGaugeInvariantWeakStarState S n
  let Fm : D.positiveTimeSubalgebra.toSubmodule :=
    ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩
  let Gm : D.positiveTimeSubalgebra.toSubmodule :=
    ⟨(G : physicalYangMillsGaugeInvariantObservableSubalgebra S), G.property⟩
  have hpolarization :=
    D.osBilinForm_eq_quadratic_polarization omega (hInvariant n) F G
  change D.osBilinForm omega Fm Gm = _
  rw [hpolarization]
  have hFG :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_expectation_eq_finite_reflectedIntegral
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent N hN beta hbeta
      (D.quadraticBoundedContinuousFunction (F + G))
      (B.finiteBridge (F + G)) n
  have hF :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_expectation_eq_finite_reflectedIntegral
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent N hN beta hbeta
      (D.quadraticBoundedContinuousFunction F)
      (B.finiteBridge F) n
  have hG :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_expectation_eq_finite_reflectedIntegral
      S.toPhysicalFourDimensionalYangMillsWeakLimit
      halfExtent N hN beta hbeta
      (D.quadraticBoundedContinuousFunction G)
      (B.finiteBridge G) n
  have hFG' :
      omega (D.quadraticObservable (F + G)) =
        ∫ A,
          periodicHypercubicEvenFullReflectedObservable
            (halfExtent n)
            ((B.finiteBridge (F + G)).positiveHalfObservable n) A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure := by
    rw [show omega =
        physicalYangMillsApproximatingGaugeInvariantWeakStarState S n by rfl]
    rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
      physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
    simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction]
      using hFG
  have hF' :
      omega (D.quadraticObservable F) =
        ∫ A,
          periodicHypercubicEvenFullReflectedObservable
            (halfExtent n)
            ((B.finiteBridge F).positiveHalfObservable n) A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure := by
    rw [show omega =
        physicalYangMillsApproximatingGaugeInvariantWeakStarState S n by rfl]
    rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
      physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
    simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction]
      using hF
  have hG' :
      omega (D.quadraticObservable G) =
        ∫ A,
          periodicHypercubicEvenFullReflectedObservable
            (halfExtent n)
            ((B.finiteBridge G).positiveHalfObservable n) A
          ∂(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength (halfExtent n))
            N hN (beta n) (hbeta n)).gibbsMeasure := by
    rw [show omega =
        physicalYangMillsApproximatingGaugeInvariantWeakStarState S n by rfl]
    rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply,
      physicalYangMillsApproximatingGaugeInvariantExpectation_apply]
    simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.quadraticBoundedContinuousFunction]
      using hG
  rw [hFG', hF', hG']
  rfl

/-- Audit-visible receipt that the quadratic physical weak-star bridge already
controls the full reflected OS cross form by polarization. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSPolarizedFiniteIntegralBridgePackage
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  crossForm :
    ∀ (n : ℕ) (F G : D.positiveTimeSubalgebra),
      let Fm : D.positiveTimeSubalgebra.toSubmodule :=
        ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S), F.property⟩
      let Gm : D.positiveTimeSubalgebra.toSubmodule :=
        ⟨(G : physicalYangMillsGaugeInvariantObservableSubalgebra S), G.property⟩
      D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          Fm Gm =
        physicalYangMillsEvenPeriodicWilsonOSFinitePolarizedReflectedIntegral
          S D halfExtent N hN beta hbeta B n F G

/-- Construct the polarized finite-integral bridge package from the existing
quadratic weak-star bridge and reflection invariance. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_polarizedFiniteIntegralBridgePackage
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSPolarizedFiniteIntegralBridgePackage
      S D halfExtent N hN beta hbeta B hInvariant :=
  { crossForm :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_eq_finitePolarizedReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant }

end

end MathlibAnalytic
end MGAP4D
