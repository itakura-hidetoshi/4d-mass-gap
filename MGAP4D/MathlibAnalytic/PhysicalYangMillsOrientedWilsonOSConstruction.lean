import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticePeterWeyl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete finite-to-continuum OS-reflection package for an oriented compact
Wilson physical embedding.

The record keeps the three logically independent ingredients visible:

* the physical positive-time observable algebra and involutive reflection;
* the exact half-lattice decomposition of the compact Wilson Gibbs integral;
* the Peter--Weyl Hilbert feature factorization of the crossing kernel.

All positivity and limit-transfer fields are theorem-generated from these data. -/
structure PhysicalYangMillsOrientedWilsonOSConstruction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) where
  reflectionData :
    PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)
  halfLattice :
    PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition
      G L reflectionData
  peterWeyl :
    PhysicalYangMillsOrientedWilsonOSPeterWeylFeature halfLattice

/-- The physical continuum weak-star state selected by an OS construction. -/
noncomputable def PhysicalYangMillsOrientedWilsonOSConstruction.continuumState
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (_C : PhysicalYangMillsOrientedWilsonOSConstruction E G L) :
    WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra
        (G.toSymmetryLimit L)) :=
  physicalYangMillsContinuumGaugeInvariantWeakStarState (G.toSymmetryLimit L)

/-- Every construction record produces a continuum reflection-positive state. -/
theorem physical_yang_mills_oriented_wilson_os_construction_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSConstruction E G L) :
    C.reflectionData.WeakStarReflectionPositive C.continuumState :=
  physical_yang_mills_oriented_halfLattice_peterWeyl_continuum_reflectionPositive
    G L C.reflectionData C.halfLattice C.peterWeyl

/-- Audit-visible terminal package: the physical continuum state together with
its generated Osterwalder--Schrader reflection-positivity proof. -/
structure PhysicalYangMillsContinuumOSPositiveStatePackage
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSConstruction E G L) where
  state : WeakDual ℝ
    (physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L))
  state_eq : state = C.continuumState
  reflectionPositive : C.reflectionData.WeakStarReflectionPositive state

/-- Build the terminal continuum OS-positive state package. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSConstruction.toContinuumOSPositiveStatePackage
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSConstruction E G L) :
    PhysicalYangMillsContinuumOSPositiveStatePackage C where
  state := C.continuumState
  state_eq := rfl
  reflectionPositive :=
    physical_yang_mills_oriented_wilson_os_construction_reflectionPositive C

@[simp]
theorem PhysicalYangMillsOrientedWilsonOSConstruction.continuumPackage_state
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSConstruction E G L) :
    C.toContinuumOSPositiveStatePackage.state = C.continuumState :=
  rfl

end

end MathlibAnalytic
end MGAP4D
