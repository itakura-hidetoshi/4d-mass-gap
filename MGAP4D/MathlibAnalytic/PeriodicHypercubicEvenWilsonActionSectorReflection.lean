import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionExactSectors
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionReflection

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Reindexing a finite plaquette sum by the orientation-corrected reflection
permutation leaves the sum unchanged. -/
theorem periodicHypercubicEvenPlaquette_sum_reflection
    {M : Type*} [AddCommMonoid M]
    (H : ℕ) (f : PeriodicHypercubicEvenPlaquette H → M) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      f (periodicHypercubicEvenPlaquetteReflection H p)) =
      ∑ p : PeriodicHypercubicEvenPlaquette H, f p := by
  simpa [periodicHypercubicEvenPlaquetteReflectionEquiv] using
    (periodicHypercubicEvenPlaquetteReflectionEquiv H).sum_comp f

end

end MathlibAnalytic
end MGAP4D
