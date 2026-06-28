import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalKernelProduct

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-to-continuum OS construction using scale-dependent local crossing
kernels.

Unlike the common-feature construction, the global Peter--Weyl Hilbert space
is generated separately at every lattice scale from the finite ordered list of
crossing plaquettes.  This matches periodic lattice families whose number of
crossing plaquettes grows with the scale. -/
structure PhysicalYangMillsOrientedWilsonOSLocalConstruction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding)
    (G : E.PhysicalGaugeAction)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) where
  reflectionData :
    PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)
  halfLattice :
    PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition
      G L reflectionData
  localKernelProduct :
    PhysicalYangMillsOrientedWilsonOSLocalKernelProductCertificate halfLattice

/-- The physical continuum weak-star state selected by the local-kernel
construction. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSLocalConstruction.continuumState
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (_C : PhysicalYangMillsOrientedWilsonOSLocalConstruction E G L) :
    WeakDual ℝ
      (physicalYangMillsGaugeInvariantObservableSubalgebra
        (G.toSymmetryLimit L)) :=
  physicalYangMillsContinuumGaugeInvariantWeakStarState (G.toSymmetryLimit L)

/-- Every local-kernel construction produces a continuum
Osterwalder--Schrader reflection-positive state. -/
theorem physical_yang_mills_oriented_wilson_os_localConstruction_reflectionPositive
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSLocalConstruction E G L) :
    C.reflectionData.WeakStarReflectionPositive C.continuumState :=
  physical_yang_mills_oriented_localKernelProduct_continuum_reflectionPositive
    G L C.reflectionData C.halfLattice C.localKernelProduct

/-- Terminal package for the physical continuum state and its generated OS
reflection-positivity proof, based only on scale-dependent local crossing
kernels. -/
structure PhysicalYangMillsContinuumLocalOSPositiveStatePackage
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSLocalConstruction E G L) where
  state : WeakDual ℝ
    (physicalYangMillsGaugeInvariantObservableSubalgebra
      (G.toSymmetryLimit L))
  state_eq : state = C.continuumState
  reflectionPositive : C.reflectionData.WeakStarReflectionPositive state

/-- Build the terminal continuum OS-positive state package from the
scale-dependent local crossing kernels. -/
noncomputable def
    PhysicalYangMillsOrientedWilsonOSLocalConstruction.toContinuumOSPositiveStatePackage
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSLocalConstruction E G L) :
    PhysicalYangMillsContinuumLocalOSPositiveStatePackage C where
  state := C.continuumState
  state_eq := rfl
  reflectionPositive :=
    physical_yang_mills_oriented_wilson_os_localConstruction_reflectionPositive C

@[simp]
theorem PhysicalYangMillsOrientedWilsonOSLocalConstruction.continuumPackage_state
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    (C : PhysicalYangMillsOrientedWilsonOSLocalConstruction E G L) :
    C.toContinuumOSPositiveStatePackage.state = C.continuumState :=
  rfl

end

end MathlibAnalytic
end MGAP4D
