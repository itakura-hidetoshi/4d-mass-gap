import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryTightLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelProduct
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelProduct

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
* exact positive semidefiniteness and symmetry of the Wilson relative kernel;
* a generic scalar-kernel-to-RKHS Moore--Aronszajn construction;
* an exact RKHS Hilbert feature for the one-plaquette Wilson relative kernel;
* exact pullback features along concrete positive-half plaquette holonomies;
* completed tensor-product realization of finite products of local crossing kernels;
* scale-dependent couplings `beta n` in the exact local RKHS features;
* site reflection on even periodic four-dimensional lattices;
* orientation-corrected involutive reflection of periodic plaquettes;
* strict positive, strict negative, and crossing plaquette support sectors;
* a finite canonical subtype and list of all crossing plaquettes at every scale;
* automatic generation of every local feature from concrete crossing holonomies;
* scale-dependent global feature spaces generated separately at each lattice scale;
* generation of the Bochner/Hilbert Gram identity from these inputs;
* transfer of finite compact Wilson reflection positivity to the continuum state;
* terminal common-feature and scale-dependent-local construction records producing
  continuum OS-positive weak-star state packages.

The construction remains conditional on the supplied continuous physical action,
interpolation equivariance, a physical positive-time reflection, and the concrete
half-lattice Wilson-action decomposition.  For `N > 0` and every nonnegative
scale-dependent coupling `beta n`, the exact one-plaquette Wilson relative kernel
is proved symmetric and positive semidefinite as the finite-Gram limit of explicit
completed-tensor Taylor features.  Mathlib's `RKHS.OfKernel` then generates its
exact Hilbert feature without assuming Peter--Weyl coefficient positivity.

On an even periodic lattice of side length `2 (H_n + 1)`, the time reflection,
orientation-corrected plaquette reflection, geometric crossing predicate, crossing
subtype, and complete finite crossing list are now explicit.  Consequently, once
the positive-half holonomy of each concrete crossing plaquette is supplied, every
local feature and their finite completed-tensor product are generated automatically.

The remaining local analytic inputs are the exact half-lattice change of variables,
the equality of the crossing factor with the finite product of these concrete
Wilson kernels, and Bochner integrability of the amplitude-weighted global feature.
-/

end MathlibAnalytic
end MGAP4D
