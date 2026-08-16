import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalScalarOSL2Core

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter

noncomputable section

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2NeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2SecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalScalarOSCompletedL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual completed OS Hilbert vector represented by a bounded continuous
scalar observable.  The carrier and completion are the already constructed
same-root scalar OS objects; no second Hilbert completion is introduced. -/
noncomputable def periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompletedVector
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : BoundedContinuousFunction ℝ ℝ) :
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).PhysicalHilbert :=
  (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
    H N hN beta hbeta
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
    physicalVolume physicalVolume_tendsto_atTop L).physicalState
      (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCarrier
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O)

/-- Completion preserves the concrete same-root `L²(μ∞)` pairing on canonical
scalar OS vectors. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompleted_inner_eq_integral_mul
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O₁ O₂ : BoundedContinuousFunction ℝ ℝ) :
    inner ℝ
        (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompletedVector
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L O₁)
        (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompletedVector
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L O₂) =
      ∫ x, O₁ x * O₂ x ∂ProbabilityMeasure.toMeasure L.continuumMeasure := by
  let P := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
    H N hN beta hbeta
    latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
    physicalVolume physicalVolume_tendsto_atTop L
  change inner ℝ
      (P.physicalState
        (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCarrier
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L O₁))
      (P.physicalState
        (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCarrier
          H N hN beta hbeta
          latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
          physicalVolume physicalVolume_tendsto_atTop L O₂)) = _
  rw [P.inner_physicalState_physicalState]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOS_inner_eq_integral_mul
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L O₁ O₂

/-- The completed Hilbert norm squared of a canonical scalar observable is its
continuum second moment. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompleted_norm_sq_eq_integral_sq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (O : BoundedContinuousFunction ℝ ℝ) :
    ‖periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompletedVector
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L O‖ ^ 2 =
      ∫ x, O x * O x ∂ProbabilityMeasure.toMeasure L.continuumMeasure := by
  rw [← real_inner_self_eq_norm_sq]
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompleted_inner_eq_integral_mul
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L O O

/-- The constant-one completed scalar vector is exactly the canonical OS
vacuum already constructed from the normalized continuum state. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompleted_one_eq_vacuum
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    let P := periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L
    periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSCompletedVector
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L
        (1 : BoundedContinuousFunction ℝ ℝ) =
      P.vacuum := by
  dsimp only
  unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.vacuum
  apply congrArg
    (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop L).physicalState
  apply
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.Carrier.observable_injective
      (periodicHypercubicEvenRestrictedBoundaryVacuumScalarOSPreHilbertData
        H N hN beta hbeta
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop L)
  rfl

end

end MathlibAnalytic
end MGAP4D
