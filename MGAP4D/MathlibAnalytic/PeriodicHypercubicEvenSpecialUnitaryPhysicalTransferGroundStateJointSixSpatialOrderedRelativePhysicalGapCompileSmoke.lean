import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOrderedRelativePhysicalGap

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open MeasureTheory

noncomputable section

#check sixSpatial_ordered_relativePoincare_rightBoundary
#check sixSpatial_ordered_relativeFrame_of_retainedContraction
#check sixSpatial_ordered_relativeFrame_implies_transferGap_of_retainedContraction
#check PeriodicHypercubicEvenSpecialUnitaryHasUniformOrderedRetainedBoundaryContraction
#check periodicHypercubicEvenSpecialUnitary_uniformOrderedRetainedBoundaryContraction_implies_uniformTransferGap

-- Finite-volume receiver: retained-boundary contraction is the only new quantitative input.
example
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract :
      ∀ x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
        ‖allRightLeftRetainedCondExpL2 H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
              H N hN beta hbeta
              (((x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
                Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)))))‖ ^ 2
          ≤ rho *
            ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  exact sixSpatial_ordered_relativeFrame_implies_transferGap_of_retainedContraction
    H N hN beta hbeta s hs hcut rho hrho0 hrho1 hcontract

#print axioms sixSpatial_ordered_relativePoincare_rightBoundary
#print axioms sixSpatial_ordered_relativeFrame_of_retainedContraction
#print axioms sixSpatial_ordered_relativeFrame_implies_transferGap_of_retainedContraction
#print axioms periodicHypercubicEvenSpecialUnitary_uniformOrderedRetainedBoundaryContraction_implies_uniformTransferGap

end
