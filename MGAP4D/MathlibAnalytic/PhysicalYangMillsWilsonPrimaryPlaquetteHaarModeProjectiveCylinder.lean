import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryHaarProjectiveCylinderOrthonormal
import Mathlib.Order.Filter.Finite

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

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

/-- Exact one-step realization of a normalized-Haar `SU(N)` plaquette mode in
one selected projective finite marginal.

The map is the composition

`single normalized-Haar holonomy L²`
`→ actual canonical primary-plaquette boundary Haar L²`
`→ interacting/projective finite-marginal L²`.

The first arrow is the theorem-generated canonical plaquette isometry from
#1613; the second is the density-corrected projective boundary readout. -/
noncomputable def primarySpatialPlaquetteHaarProjectiveL2Isometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.boundaryHaarProjectiveL2Isometry n).comp
    (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback
      (halfExtent n) N)

/-- A normalized-Haar orthonormal family remains orthonormal after exact
canonical-primary-plaquette realization in any selected projective marginal. -/
theorem primarySpatialPlaquetteHaarProjectiveL2Isometry_orthonormal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ)
    {κ : Type*}
    (v : κ → SpecialUnitaryNormalizedHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((R.primarySpatialPlaquetteHaarProjectiveL2Isometry n) ∘ v) :=
  hv.comp_linearIsometry (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Model-facing primary-plaquette Haar-mode realization data.

Compared with
`PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData`,
this removes the finite-set-by-finite-set existential choice of an orthonormal
boundary Haar family.  Instead there is one global normalized-Haar orthonormal
mode family.  Its actual primary-plaquette images are required to be the
projective cylinder vectors; finite boundary Haar realizations are then
constructed canonically by restriction and exact `LinearIsometry` transport.
-/
structure PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
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
  haarMode : ℕ → SpecialUnitaryNormalizedHaarL2 N
  haarMode_orthonormal : Orthonormal ℝ haarMode
  primaryPlaquetteHaarMode_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    R.primarySpatialPlaquetteHaarProjectiveL2Isometry n (haarMode k) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData

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

/-- Eventual support of individual cylinder modes automatically upgrades to
simultaneous eventual support of every finite selected family. -/
theorem finiteSupportEventually
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    ∀ᶠ n in atTop,
      s.biUnion C.cylinderIndex ⊆ R.marginalIndex n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      filter_upwards [C.supportEventually a, ih] with n haNow hsNow
      simpa only [Finset.biUnion_insert] using
        (Finset.union_subset.mpr ⟨haNow, hsNow⟩)

/-- Every finite selected cylinder family therefore has one actual Wilson scale
whose projective marginal contains its common support. -/
theorem existsFiniteCommonScale
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    ∃ n : ℕ,
      s.biUnion C.cylinderIndex ⊆ R.marginalIndex n :=
  (C.finiteSupportEventually s).exists

/-- The old finite boundary-Haar existential is theorem-generated from one
global normalized-Haar orthonormal family.

At the common scale, restrict the global mode family to the subtype `s`, then
transport it through the exact primary-plaquette boundary `LinearIsometry`.
The projective realization equality follows from the single composite isometry
and `primaryPlaquetteHaarMode_eq_transition`. -/
theorem finiteBoundaryHaarOrthonormalRealization
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    ∃ n : ℕ,
      ∃ hCommon : s.biUnion C.cylinderIndex ⊆ R.marginalIndex n,
        ∃ haarVector :
            s → PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N,
          Orthonormal ℝ haarVector ∧
          ∀ i : s,
            R.boundaryHaarProjectiveL2Isometry n (haarVector i) =
              EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
                (F := F)
                ((Finset.subset_biUnion_of_mem C.cylinderIndex i.property).trans hCommon)
                (C.cylinderVector (i : ℕ)) := by
  classical
  rcases C.existsFiniteCommonScale s with ⟨n, hCommon⟩
  let v : s → SpecialUnitaryNormalizedHaarL2 N :=
    fun i => C.haarMode (i : ℕ)
  have hv : Orthonormal ℝ v := by
    exact C.haarMode_orthonormal.comp
      (fun i : s => (i : ℕ)) Subtype.val_injective
  let haarVector :
      s → PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N :=
    fun i =>
      periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback
        (halfExtent n) N (v i)
  have hHaar : Orthonormal ℝ haarVector := by
    simpa [haarVector, Function.comp_def] using
      (periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback_orthonormal
        (halfExtent n) N v hv)
  refine ⟨n, hCommon, haarVector, hHaar, ?_⟩
  intro i
  have h :=
    (Finset.subset_biUnion_of_mem C.cylinderIndex i.property).trans hCommon
  simpa [haarVector, v,
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout.primarySpatialPlaquetteHaarProjectiveL2Isometry]
    using C.primaryPlaquetteHaarMode_eq_transition (i : ℕ) n h

/-- Package the theorem-generated finite boundary-Haar realizations into the
exact interface consumed by the existing projective-cylinder strictness route. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := C.cylinderIndex
  cylinderVector := C.cylinderVector
  supportEventually := C.supportEventually
  finiteImage_eq_transition := C.finiteImage_eq_transition
  finiteBoundaryHaarOrthonormalRealization := C.finiteBoundaryHaarOrthonormalRealization

/-- A single normalized-Haar orthonormal primary-plaquette mode family therefore
theorem-generates common-projective-marginal orthonormality. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant :=
  C.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData.toFiniteProjectiveCylinderOrthonormalData

/-- Primary-plaquette normalized-Haar mode realization theorem-generates the
strict continuum finite-Gram physical carrier through the existing chain

`global Haar orthonormal family`
`→ actual primary-plaquette boundary Haar`
`→ projective finite marginal orthonormality`
`→ finite linear independence`
`→ tail-uniform Wilson OS coercivity`
`→ continuum Gram PosDef`. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) :=
  C.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData.toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData

end

end MathlibAnalytic
end MGAP4D
