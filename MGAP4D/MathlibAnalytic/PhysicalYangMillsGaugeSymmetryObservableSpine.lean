import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedGaugeSymmetryTightLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSLocalConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSConcreteLocalKernelProduct
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelProduct
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedMeasureFactorization
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedBochnerFactorization
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedHaarFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryBoundaryFiberedGibbsFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSHalfLatticeProductFactorization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBoundaryFiberedBochnerGram
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSBoundaryFiberedCoordinateConstruction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicHolonomyMeasurableAmplitudeBoundedLocalKernelProduct

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
* density transport from the split Gibbs law to a product half-reference measure;
* generation of the iterated kernel formula by `integral_map`, `withDensity`, and Fubini;
* an exact coordinate equivalence from full edge configurations to shared fixed-plane
  boundary data together with positive and negative open-half configurations;
* an exact pushforward-measure interface for those boundary-fibered coordinates;
* two-stage Fubini transport from full-configuration integrals to boundary/half/half integrals;
* a generic boundary-fibered measure-to-Bochner Gram theorem;
* a generic finite-`pi` product-measure factorization under every involutive edge partition;
* an exact boundary/open-half/open-half factorization of compact Wilson product Haar laws;
* exact transport of continuous compact Wilson Gibbs laws to the boundary-fibered Haar law;
* a physical positive-link reflection and side partition on even periodic lattices;
* a concrete periodic `SU(N)` normalized-Haar pushforward identity;
* a concrete periodic `SU(N)` boundary-fibered Gibbs-density pushforward identity;
* a boundary-fibered decomposition retaining shared reflection-fixed-plane variables;
* conditional Bochner Gram reduction over each fixed boundary configuration;
* a concrete coordinate-to-physical-pullback constructor producing finite-volume and
  continuum Osterwalder--Schrader reflection positivity;
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
* generation of feature measurability from measurable positive-half holonomies;
* a local-kernel-product certificate with all measurable and Bochner-integrable data;
* an exact measurable amplitude/kernel product constructor at every even periodic scale.
-/

end MathlibAnalytic
end MGAP4D
