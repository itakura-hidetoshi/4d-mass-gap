import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedJointTemporalContinuity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsContinuumEuclideanTimeTranslation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeDiscreteTemporalCompatibility

/-- Joint continuity discharges the varying-time weak-limit continuity input in
the continuum temporal-symmetry constructor. -/
noncomputable def toContinuumEuclideanTimeTranslationOfJointContinuity
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {A : E.PhysicalDiscreteTemporalAction}
    (C : E.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (D : A.DenseTemporalApproximation)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation
      (G.toSymmetryLimit L) :=
  C.toContinuumEuclideanTimeTranslation
    (J.toWeakLimitContinuity D L)

/-- Full discrete-to-continuum temporal bridge.

When the finite-scale time homomorphism is `k ↦ k * latticeSpacing n`, positive
lattice spacings tending to zero generate the required dense time approximation
by the floor selector.  Joint continuity then transports the exact finite-scale
invariance to all real times of the continuum law. -/
noncomputable def toContinuumEuclideanTimeTranslationOfFloor
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {A : E.PhysicalDiscreteTemporalAction}
    (C : E.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding) :
    PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation
      (G.toSymmetryLimit L) :=
  C.toContinuumEuclideanTimeTranslationOfJointContinuity J
    (ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction.DenseTemporalApproximation.ofFloor
      latticeTime_eq) L

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.GaugeDiscreteTemporalCompatibility

end

end MathlibAnalytic
end MGAP4D
