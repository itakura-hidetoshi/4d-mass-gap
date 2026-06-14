import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsOSPhysicalSemigroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) where
  operator : ℝ → M.observables.PhysicalHilbert →L[ℝ]
    M.observables.PhysicalHilbert
  zero_apply : ∀ psi, operator 0 psi = psi
  add_apply :
    ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ psi,
      operator (s + t) psi = operator s (operator t psi)
  vacuum_fixed :
    ∀ t : ℝ, 0 ≤ t → operator t M.vacuum = M.vacuum
  contraction :
    ∀ (t : ℝ), 0 ≤ t → ∀ psi, ‖operator t psi‖ ≤ ‖psi‖

end

end MathlibAnalytic
end MGAP4D
