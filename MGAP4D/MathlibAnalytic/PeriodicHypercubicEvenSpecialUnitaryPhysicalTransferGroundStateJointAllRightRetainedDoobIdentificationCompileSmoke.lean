import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointAllRightRetainedDoobIdentification

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open MeasureTheory

noncomputable section

#check leftBoundaryL2Isometry_surjective_onto_leftRetained
#check allRightLeftRetainedCondExpL2_eq_coarseCondExp
#check allRightLeftRetainedCondExpL2_rightBoundary_eq_leftBoundary_doob
#check allRightLeftRetainedCondExpL2_rightBoundary_norm_eq_doob
#check retainedBoundaryContraction_iff_doobContraction

-- The literal retained conditional expectation and the old coarse projection
-- are the same operator on the same genuine joint L2 carrier.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    allRightLeftRetainedCondExpL2 H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
        H N hN beta hbeta :=
  allRightLeftRetainedCondExpL2_eq_coarseCondExp H N hN beta hbeta

#print axioms leftBoundaryL2Isometry_surjective_onto_leftRetained
#print axioms allRightLeftRetainedCondExpL2_eq_coarseCondExp
#print axioms allRightLeftRetainedCondExpL2_rightBoundary_eq_leftBoundary_doob
#print axioms retainedBoundaryContraction_iff_doobContraction

end
