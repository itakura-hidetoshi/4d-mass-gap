import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopBetaContinuity

/-!
# Regression tests for the existing canonical nonnegative vacuum

Neither endpoint supplies a continuous choice, a phase selection, or a spectral
gap continuity hypothesis. Both refer to the original canonical vacuum.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta.1 beta.2) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_halfLine_continuous
      H N hN

example (H N : ℕ) (hN : 0 < N) :
    Continuous
      (fun beta : Set.Ici (0 : ℝ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H N hN beta.1 beta.2)) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ofReal_halfLine_continuous
      H N hN

end
end MGAP4D.MathlibAnalytic
