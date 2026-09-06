import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridgeAudit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Final single theorem carrier for the scale-uniform one-slab reduction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridge_final
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridgePackage
      halfExtent N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridgePackage
    halfExtent N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
