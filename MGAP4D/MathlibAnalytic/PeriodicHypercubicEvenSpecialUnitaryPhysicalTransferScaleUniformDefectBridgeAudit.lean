import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compact audit theorem exposing the entire current scale-uniform reduction in
one statement.  It is intentionally assumption-free beyond the actual finite
Wilson family parameters: it does not assert that either equivalent condition
holds. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabScaleUniformDefectBridge_audit
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
        halfExtent N hN beta hbeta ↔
      PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
        halfExtent N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitary_uniformRawDefect_iff_uniformTransferGap
    halfExtent N hN beta hbeta

end

end MathlibAnalytic
end MGAP4D
