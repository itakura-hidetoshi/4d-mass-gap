import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeSymmetryObservableSpine
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasureInstances
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedDensityBochnerFactorization
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedDensityBochner
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBoundaryFiberedGibbsBochner

namespace MGAP4D
namespace MathlibAnalytic

/-!
# Physical Yang--Mills Gibbs--Bochner observable spine

This terminal aggregate extends the gauge-symmetry observable spine with:

* structural `SFinite` instances for finite boundary and open-half product measures;
* exact transport of an interacting compact Wilson Gibbs law to one shared
  reflection-fixed boundary and two open-half Haar coordinates;
* a density-weighted boundary-fibered Bochner--Fubini theorem;
* reduction of actual compact Wilson expectations to boundary integrals of
  squared conditional Hilbert moments;
* scale-dependent physical pullback nonnegativity;
* approximating and continuum Osterwalder--Schrader reflection positivity.

The remaining model-specific input is the pointwise identification of the
transported Wilson density times the reflected observable with the inner
product of the concrete boundary-dependent crossing-kernel features.
-/

end MathlibAnalytic
end MGAP4D
