import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDiscreteFloorSelfAdjointness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSQuadraticStrongContinuity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
namespace PositiveTimeObservableContractionSemigroup
namespace ContinuumTimeReflectionBridge

/-- Exact finite integer temporal translations, floor dense-time approximation,
joint continuity, continuum reflection compatibility, and continuity at zero of
the scalar OS quadratic difference imply self-adjointness of the graph-closed OS
Hamiltonian.

The Hilbert-valued strong-continuity input is generated internally from the
quadratic expectation. -/
theorem closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor_ofOSQuadraticContinuity
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
    (hQuadratic : T.OSQuadraticContinuityAtZero) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hQuadratic.toStrongContinuityOnObservableStates).closedRightHamiltonian := by
  exact closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor
    C J latticeTime_eq L H hQuadratic.toStrongContinuityOnObservableStates

end ContinuumTimeReflectionBridge
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
