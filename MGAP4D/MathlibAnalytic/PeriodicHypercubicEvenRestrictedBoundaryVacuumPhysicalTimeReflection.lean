import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalOSBilinearLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedConfigurationReflection

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance restrictedBoundaryVacuumPhysicalTimeReflectionNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance restrictedBoundaryVacuumPhysicalTimeReflectionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance restrictedBoundaryVacuumPhysicalTimeReflectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance restrictedBoundaryVacuumPhysicalTimeReflectionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance restrictedBoundaryVacuumPhysicalTimeReflectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance restrictedBoundaryVacuumPhysicalTimeReflectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Physical Euclidean time reflection fixes the canonical shared boundary
restriction pointwise.

The proof is geometric: every fixed-sector edge is spatial and its reflected
edge is itself.  No measure or reflection-invariance hypothesis is used. -/
theorem periodicHypercubicEven_boundaryRestriction_configurationReflection
    (H : ℕ)
    {Gauge : Type*} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction
        (periodicHypercubicEvenConfigurationReflection H A) =
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A := by
  funext e
  change periodicHypercubicEvenConfigurationReflection H A e.1 = A e.1
  have hspace : e.1.2 ≠ 0 :=
    periodicHypercubicEvenEdge_direction_ne_zero_of_side_fixed H e.1 e.2
  rw [periodicHypercubicEvenConfigurationReflection_spatial H A e.1 hspace]
  rw [periodicHypercubicEvenEdgeReflection_eq_self_of_side_fixed H e.1 e.2]

/-- The actual full-configuration restricted boundary-vacuum moment is fixed by
physical Euclidean time reflection.

This is theorem-generated from the preceding boundary-restriction identity and
the definition of the readout as a function only of the shared boundary. -/
theorem periodicHypercubicEvenRestrictedBoundaryVacuumMoment_timeReflectionInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenRestrictedBoundaryVacuumMoment
        H N hN beta hbeta A := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumMoment
  rw [periodicHypercubicEven_boundaryRestriction_configurationReflection]

/-- The concrete physical boundary-vacuum interpolation intertwines the actual
finite lattice time reflection with the identity action on its scalar physical
carrier.

Thus identity reflection on `ℝ` is not postulated for this readout: it is the
literal image of the finite Wilson lattice reflection. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding_interpolate_timeReflectionInvariant
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
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge (H n) →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let E := periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalEmbedding
      H N hN beta hbeta
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      physicalVolume physicalVolume_tendsto_atTop
    E.interpolate n
        (periodicHypercubicEvenConfigurationReflection (H n) A) =
      E.interpolate n A := by
  dsimp only
  exact
    periodicHypercubicEvenRestrictedBoundaryVacuumMoment_timeReflectionInvariant
      (H n) N hN (beta n) (hbeta n) A

end

end MathlibAnalytic
end MGAP4D
