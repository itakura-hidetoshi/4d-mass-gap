import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalTimeReflection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuum

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalScalarOSHilbertBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Osterwalder--Schrader reflection data for the scalar boundary-vacuum
readout.

All scalar observables are placed in the positive-time algebra because this
readout depends only on the shared reflection-fixed boundary sector.  Reflection
on the scalar carrier is the identity, as theorem-generated above from the
actual finite lattice time reflection fixing that boundary readout.  This is a
reflection-positive scalar subtheory, not an identification of `ℝ` with the
full Yang--Mills field configuration space. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    PhysicalYangMillsGaugeInvariantOSReflectionData
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L) where
  positiveTimeSubalgebra := ⊤
  reflection := AlgHom.id ℝ _
  reflection_involutive := fun O => rfl

@[simp]
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData_reflection_apply
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : physicalYangMillsGaugeInvariantObservableSubalgebra
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).reflection O = O := by
  rfl

/-- Every approximating weak-star state of the scalar boundary-vacuum readout is
reflection invariant under the finite-generated identity scalar reflection. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_approximating_reflectionInvariant
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let D := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  dsimp only
  intro O
  rfl

/-- Every finite scalar boundary-vacuum physical state is OS reflection
positive.

For this reflection-fixed boundary readout the OS quadratic is literally the
pointwise square `F * F`; positivity therefore follows from positivity of the
same-root probability state, with no new finite reflection-positivity premise. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_approximating_reflectionPositive
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (n : ℕ) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let D := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    D.WeakStarReflectionPositive
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n) := by
  dsimp only
  intro F
  rw [physicalYangMillsApproximatingGaugeInvariantWeakStarState_apply]
  apply physicalYangMillsApproximatingGaugeInvariantExpectation_nonneg
  intro x
  change 0 ≤ F.1.1 x * F.1.1 x
  exact mul_self_nonneg _

/-- The continuum scalar boundary-vacuum weak-star state is reflection
invariant. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_continuum_reflectionInvariant
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let D := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    D.WeakStarReflectionInvariant
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  dsimp only
  intro O
  rfl

/-- Reflection positivity passes from the same-root finite scalar states to the
continuum weak-star state through the already established weak-star
convergence. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_continuum_reflectionPositive
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    let S := periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    let D := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    D.WeakStarReflectionPositive
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S) := by
  dsimp only
  apply physical_yang_mills_gaugeInvariantWeakStarReflectionPositivity_passes_to_limit
  intro n
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_approximating_reflectionPositive
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L n

/-- The same Wilson-root continuum scalar law canonically supplies the OS
pre-Hilbert data consumed by the existing separation/completion construction. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSReflectionData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).OSPreHilbertData where
  omega :=
    physicalYangMillsContinuumGaugeInvariantWeakStarState
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)
  reflectionInvariant :=
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_continuum_reflectionInvariant
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
  reflectionPositive :=
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_continuum_reflectionPositive
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L

/-- The continuum scalar OS pre-Hilbert state is normalized. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData_isNormalized
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).IsNormalized := by
  change
    physicalYangMillsContinuumGaugeInvariantWeakStarState
        (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L) 1 = 1
  rw [physicalYangMillsContinuumGaugeInvariantWeakStarState_apply]
  exact
    physicalYangMillsContinuumGaugeInvariantExpectation_one
      (periodicHypercubicEvenRestrictedBoundaryVacuumGaugeSymmetryLimit
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)

/-- The canonical scalar OS vacuum in the completed physical Hilbert carrier has
unit norm. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_norm_vacuum
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop :
      Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    ‖(periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).vacuum‖ = 1 := by
  exact
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).norm_vacuum
      (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData_isNormalized
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)

end

end MathlibAnalytic
end MGAP4D
