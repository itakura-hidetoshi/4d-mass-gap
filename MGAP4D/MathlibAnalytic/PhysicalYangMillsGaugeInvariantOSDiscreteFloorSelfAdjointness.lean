import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumTimeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
namespace PositiveTimeObservableContractionSemigroup
namespace ContinuumTimeReflectionBridge

/-- Exact finite integer temporal translations, floor dense-time approximation,
joint continuity, continuum reflection compatibility, and observable-state strong
continuity imply self-adjointness of the graph-closed OS Hamiltonian. -/
theorem closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A) (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E₀.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T)
    (hContinuous : T.StrongContinuityOnObservableStates) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hContinuous).closedRightHamiltonian := by
  exact closedRightHamiltonian_isSelfAdjoint
    (ofDiscreteTemporalActionOfFloor C J latticeTime_eq L H) hContinuous

end ContinuumTimeReflectionBridge
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
