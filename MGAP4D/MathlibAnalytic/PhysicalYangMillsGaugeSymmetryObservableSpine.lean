import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryTightLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalConstruction
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefinite

namespace MGAP4D
namespace MathlibAnalytic

/-!
# Physical Yang--Mills gauge-symmetry observable spine

This aggregate module exposes the complete typed route

* finite oriented Wilson Gibbs gauge invariance;
* equivariant physical interpolation;
* embedded-law invariance;
* tightness and Prokhorov extraction;
* continuum measure preservation;
* measurable-event probability invariance;
* measurable-observable law invariance;
* bounded-continuous expectation invariance;
* symmetry-compatible expectation convergence;
* two-point and connected-correlation invariance and convergence;
* arbitrary finite n-point moment invariance and convergence;
* the fixed real subalgebra of pointwise gauge-invariant bounded continuous observables;
* normalized positive lattice and continuum expectation functionals;
* uniform norm bounds and continuous real-linear expectation functionals;
* normalized positive contractive continuous state packages;
* pointwise convergence of the continuous lattice states;
* weak-star convergence of the lattice state sequence to the continuum state;
* an involutive reflection on a positive-time observable subalgebra;
* weak-star closedness of reflection positivity;
* exact pullback of physical state evaluations to the original compact Wilson Gibbs laws;
* a geometric and measure-theoretic half-lattice kernel decomposition;
* an independent Peter--Weyl Hilbert feature factorization of the crossing kernel;
* the concrete one-plaquette `SU(N)` Wilson Boltzmann central function;
* the relative group kernel `k_beta(g⁻¹h)` and its half-holonomy pullback;
* a finite-dimensional real Euclidean feature for the normalized trace kernel;
* finite completed-tensor Taylor features for the Wilson exponential kernel;
* pointwise convergence of their inner products to the exact Wilson kernel;
* finite Gram positivity for every real Hilbert feature kernel;
* exact positive semidefiniteness of the one-plaquette Wilson relative kernel;
* completed tensor-product realization of finite products of local crossing kernels;
* scale-dependent global feature spaces generated separately at each lattice scale;
* generation of the Bochner/Hilbert Gram identity from these inputs;
* transfer of finite compact Wilson reflection positivity to the continuum state;
* terminal common-feature and scale-dependent-local construction records producing
  continuum OS-positive weak-star state packages.

The construction remains conditional on the supplied continuous physical action,
interpolation equivariance, a physical positive-time reflection, and the concrete
half-lattice Wilson-action decomposition.  For `N > 0` and `beta >= 0`, the exact
one-plaquette Wilson relative kernel is now proved positive semidefinite as the
finite-Gram limit of explicit completed-tensor Taylor features, without assuming
Peter--Weyl coefficient positivity.  Producing the exact `RealHilbertKernelFeature`
record from this theorem remains the generic Moore--Aronszajn/GNS completion step.
-/

end MathlibAnalytic
end MGAP4D
