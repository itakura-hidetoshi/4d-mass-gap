import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveFiniteMarginalL2TransitionTrans
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProjectiveCylinderOrthonormalStrictness

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

/-- Density-corrected boundary Haar `L²` embeds isometrically into the selected
projective finite marginal at one Wilson scale.

This is the two-step isometry

`boundary Haar L² → interacting boundary marginal L² → projective marginal L²`.
-/
noncomputable def boundaryHaarProjectiveL2Isometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N →ₗᵢ[ℝ]
      Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
  (R.boundaryMarginalL2Pullback n).comp
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
      (halfExtent n) N hN (beta n) (hbeta n))

/-- Boundary-Haar orthonormality is preserved exactly after density correction
and projective boundary readout. -/
theorem boundaryHaarProjectiveL2Isometry_orthonormal
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ)
    {ι : Type*}
    (v : ι → PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ ((R.boundaryHaarProjectiveL2Isometry n) ∘ v) :=
  hv.comp_linearIsometry (R.boundaryHaarProjectiveL2Isometry n)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- A model-facing boundary-Haar realization of the finite projective-cylinder
orthonormal strictness required by #1608.

For every finite selected family, one sufficiently large Wilson scale is chosen
whose projective marginal contains the common cylinder support.  At that scale
one asks for an orthonormal family in the actual boundary Haar `L²` space whose
density-corrected projective images agree exactly with the transitioned fixed
cylinder vectors.

The orthonormality itself is therefore localized entirely to boundary Haar,
where compact-group Peter--Weyl/character orthogonality belongs. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
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
  finiteBoundaryHaarOrthonormalRealization : ∀ s : Finset ℕ,
    ∃ n : ℕ,
      ∃ hCommon : s.biUnion cylinderIndex ⊆ R.marginalIndex n,
        ∃ haarVector :
            s → PeriodicHypercubicEvenBoundaryHaarL2 (halfExtent n) N,
          Orthonormal ℝ haarVector ∧
          ∀ i : s,
            R.boundaryHaarProjectiveL2Isometry n (haarVector i) =
              EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
                (F := F)
                ((Finset.subset_biUnion_of_mem cylinderIndex i.property).trans hCommon)
                (cylinderVector (i : ℕ))

namespace PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData

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

/-- Boundary-Haar orthonormal realization at one sufficiently large scale
forces orthonormality on the common finite cylinder marginal.

The forward direction uses the composite boundary-Haar/projective isometry.
The reverse step is legitimate because the common-to-large projective
transition is itself a `LinearIsometry`; `LinearIsometry.orthonormal_comp_iff`
then reflects orthonormality back to the common marginal. -/
theorem finiteCommonMarginalOrthonormal
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (s : Finset ℕ) :
    Orthonormal ℝ
      (fun i : s =>
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F)
          (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
          (C.cylinderVector (i : ℕ))) := by
  rcases C.finiteBoundaryHaarOrthonormalRealization s with
    ⟨n, hCommon, haarVector, hHaar, hRealize⟩
  let u : s → Lp ℝ 2 (F.finiteMarginal (s.biUnion C.cylinderIndex)) :=
    fun i =>
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F)
        (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
        (C.cylinderVector (i : ℕ))
  let e :
      Lp ℝ 2 (F.finiteMarginal (s.biUnion C.cylinderIndex)) →ₗᵢ[ℝ]
        Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
    EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F) hCommon
  have hHaarLarge :
      Orthonormal ℝ ((R.boundaryHaarProjectiveL2Isometry n) ∘ haarVector) :=
    R.boundaryHaarProjectiveL2Isometry_orthonormal n haarVector hHaar
  have hFamily :
      e ∘ u = (R.boundaryHaarProjectiveL2Isometry n) ∘ haarVector := by
    funext i
    change
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hCommon
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F)
            (Finset.subset_biUnion_of_mem C.cylinderIndex i.property)
            (C.cylinderVector (i : ℕ))) =
        R.boundaryHaarProjectiveL2Isometry n (haarVector i)
    rw [L.finiteMarginalL2Transition_trans]
    exact (hRealize i).symm
  have hLarge : Orthonormal ℝ (e ∘ u) := by
    rw [hFamily]
    exact hHaarLarge
  have hCommonOrthonormal : Orthonormal ℝ u :=
    (e.orthonormal_comp_iff).mp hLarge
  simpa [u] using hCommonOrthonormal

/-- Forget the boundary-Haar realization layer and recover exactly the
projective-cylinder orthonormal datum integrated in #1608. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := C.cylinderIndex
  cylinderVector := C.cylinderVector
  supportEventually := C.supportEventually
  finiteImage_eq_transition := C.finiteImage_eq_transition
  finiteCommonMarginalOrthonormal := C.finiteCommonMarginalOrthonormal

/-- Boundary-Haar orthonormal cylinder realization theorem-generates the exact
strict continuum finite-Gram physical carrier through #1608 and #1607. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) :=
  PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData.toFiniteOSGramPosDefPhysicalCarrierData
    C.toFiniteProjectiveCylinderOrthonormalData

end PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData

end

end MathlibAnalytic
end MGAP4D
