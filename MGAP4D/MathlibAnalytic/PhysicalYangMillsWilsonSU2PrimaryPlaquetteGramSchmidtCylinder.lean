import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- The positive-rank witness used by the concrete `SU(2)` Wilson cylinder
specialization. -/
theorem specialUnitaryTwoWilsonRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance specialUnitaryTwoWilsonGramSchmidtCylinderNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Model-facing cylinder data specialized to the theorem-generated `SU(2)`
Wilson-energy Gram--Schmidt family.

Unlike the generic primary-plaquette Haar-mode interface, this structure has no
`haarMode` field and no orthonormality field.  Both are fixed by theorem to the
Mathlib Gram--Schmidt orthonormalization of the concrete Wilson-energy power
family.  The only remaining mode-realization obligation is the physical one:
the selected cylinder vector must agree with that explicit primary-plaquette
projective mode at every containing marginal. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
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
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)
  primaryPlaquetteGramSchmidtMode_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Forget only the theorem-generated specialization: an `SU(2)` Wilson-energy
Gram--Schmidt cylinder package canonically supplies the generic primary-
plaquette Haar-mode interface. -/
noncomputable def toPrimaryPlaquetteHaarModeCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := C.cylinderIndex
  cylinderVector := C.cylinderVector
  supportEventually := C.supportEventually
  finiteImage_eq_transition := C.finiteImage_eq_transition
  haarMode := specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode
  haarMode_orthonormal :=
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal
  primaryPlaquetteHaarMode_eq_transition := by
    intro k n h
    simpa [PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode]
      using C.primaryPlaquetteGramSchmidtMode_eq_transition k n h

/-- The specialized cylinder package theorem-generates the old finite boundary-
Haar orthonormal realization without any Haar-family existential input. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toPrimaryPlaquetteHaarModeCylinderData.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData

/-- The specialized cylinder package theorem-generates common-projective-
marginal orthonormality through the exact primary-plaquette isometries. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toPrimaryPlaquetteHaarModeCylinderData.toFiniteProjectiveCylinderOrthonormalData

/-- The explicit `SU(2)` Wilson-energy Gram--Schmidt cylinder realization is
therefore enough to theorem-generate the strict continuum finite-Gram physical
carrier.  The abstract normalized-Haar orthonormal-family input has disappeared
from this specialization. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant) :=
  C.toPrimaryPlaquetteHaarModeCylinderData.toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData

end

end MathlibAnalytic
end MGAP4D
