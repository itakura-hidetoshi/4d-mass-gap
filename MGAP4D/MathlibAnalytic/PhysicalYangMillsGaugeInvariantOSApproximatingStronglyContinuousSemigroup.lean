import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianSemigroupCovariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Strong continuity of the actual finite-volume Wilson OS semigroup at every
scale, stated on the dense family represented by positive-time observables.

Contractivity and density then construct a canonical strongly continuous
semigroup on each completed finite Wilson OS Hilbert space. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) : Prop where
  strongContinuity :
    ∀ n,
      (C.toPositiveTimeObservableContractionSemigroup n).StrongContinuityOnObservableStates

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData

variable
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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The canonical strongly continuous contraction semigroup on the `n`-th
completed finite Wilson OS Hilbert space. -/
noncomputable def finiteStronglyContinuousPhysicalSemigroup
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData C)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).StronglyContinuousPhysicalSemigroup :=
  PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
    (C.toPositiveTimeObservableContractionSemigroup n)
    (R.strongContinuity n)

/-- Strong-continuity completion retains the previously constructed finite
physical contraction semigroup. -/
@[simp] theorem finiteStronglyContinuousPhysicalSemigroup_toPhysicalSemigroup
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData C)
    (n : ℕ) :
    (R.finiteStronglyContinuousPhysicalSemigroup n).toPhysicalSemigroup =
      C.finitePhysicalSemigroup n :=
  rfl

/-- Consequently its time-`t` operator is the actual finite Wilson OS operator. -/
@[simp] theorem finiteStronglyContinuousPhysicalSemigroup_operator
    (R : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData C)
    (n : ℕ) (t : NNReal) :
    (R.finiteStronglyContinuousPhysicalSemigroup n).toPhysicalSemigroup.operator t =
      C.finiteOperator n t :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
