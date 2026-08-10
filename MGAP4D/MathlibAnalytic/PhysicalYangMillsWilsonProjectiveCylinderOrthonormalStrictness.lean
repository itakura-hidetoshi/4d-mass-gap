import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProjectiveCylinderFiniteOSGramPosDefPhysicalCarrier
import Mathlib.Analysis.InnerProductSpace.Orthonormal

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- A Peter--Weyl-friendly strengthening of the finite projective-cylinder
strictness datum.

Instead of assuming finite common-marginal linear independence directly, this
interface asks that every finite selected family, after transition to its common
projective marginal, is orthonormal in the real `L²` space.  Mathlib's
`Orthonormal.linearIndependent` then theorem-generates the strictness input used
by the tail-coercivity package.

This formulation is designed for the next compact-group step: construct
boundary-Haar Peter--Weyl vectors, transport them through the already-proved
reciprocal-vacuum density isometry into the interacting marginal, and use exact
projective compatibility. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  cylinderIndex : ℕ → Finset EuclideanFourSpace
  cylinderVector : ∀ k,
    Lp ℝ 2 (F.finiteMarginal (cylinderIndex k))
  supportEventually : ∀ k,
    ∀ᶠ n in atTop, cylinderIndex k ⊆ R.marginalIndex n
  finiteImage_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)
  finiteCommonMarginalOrthonormal : ∀ s : Finset ℕ,
    Orthonormal ℝ
      (fun i : s =>
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (Finset.subset_biUnion_of_mem cylinderIndex i.property)
          (cylinderVector (i : ℕ)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Mathlib turns common-marginal orthonormality into the exact finite linear
independence hypothesis consumed by the #1607 projective-cylinder package. -/
theorem finiteCommonMarginalLinearIndependent
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    LinearIndependent ℝ
      (fun i : s =>
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
          (C.cylinderVector (i : ℕ))) :=
  (C.finiteCommonMarginalOrthonormal s).linearIndependent

/-- Forget only the orthonormal strengthening and recover the exact finite
projective-cylinder linear-independence datum integrated in #1607. -/
noncomputable def toFiniteProjectiveCylinderLinearIndependentData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData
      S D halfExtent N hN beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := C.cylinderIndex
  cylinderVector := C.cylinderVector
  supportEventually := C.supportEventually
  finiteImage_eq_transition := C.finiteImage_eq_transition
  finiteCommonMarginalLinearIndependent := C.finiteCommonMarginalLinearIndependent

/-- Common-marginal orthonormality theorem-generates eventual projective `L²`
coherence and therefore tail-uniform finite Wilson OS coercivity. -/
noncomputable def toProjectiveL2EventuallyCoherentPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSProjectiveL2EventuallyCoherentPhysicalCarrierData
      S D halfExtent N hN beta hbeta Q F R L hInvariant :=
  PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData.toProjectiveL2EventuallyCoherentPhysicalCarrierData
    C.toFiniteProjectiveCylinderLinearIndependentData

/-- Finite projective-cylinder orthonormality theorem-generates the exact
strict continuum finite-Gram physical-carrier datum.  The route is

`orthonormal common marginal`
`→ finite linear independence`
`→ tail-uniform Wilson OS coercivity`
`→ continuum Gram PosDef`.
-/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) :=
  PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderLinearIndependentData.toFiniteOSGramPosDefPhysicalCarrierData
    C.toFiniteProjectiveCylinderLinearIndependentData

end PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData

end

end MathlibAnalytic
end MGAP4D
