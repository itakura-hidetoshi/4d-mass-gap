import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllDepthGIKernelFaithfulnessV5_OW
import Mathlib.Tactic

/-!
# P4-Q2-OX — unconditional genuine Wilson GL mass positivity at all finite depths

OW proved that, for the UNMODIFIED two-interacting-posterior Wilson
signed receiver, actual HJ physical and all-context GI kernels coincide
at ALL finite right-Krylov depths, every nonnegative fine coupling,
and every positive frozen Wilson coupling. No depth-two source-rank
or Schur physical nonzero hypothesis is needed.

OR already proved, directly from the genuinely positive original
posterior density-contrast Haar variance and square of the true signed
GI response, the all-depth GL mass zero-locus equivalence and strict
positive mass whenever the physical/GI kernels coincide.

We now eliminate OR's historical quadratic-collapse Schur branch
and small-positive-fine restriction ENTIRELY. At EVERY finite volume,
EVERY frozen coupling b>0, EVERY nonnegative fine coupling t>=0,
EVERY finite depth r and signed coefficient vector a, for the SAME
true Gauss-law physical Wilson source S_r a:

  M_GL(S_r a)=0  <->  S_r a=0
  S_r a != 0  ->  M_GL(S_r a)>0.

These are GENUINE original Wilson posterior results; they are NOT
quantitative volume/fine/depth-uniform lower bounds. They do not prove
S_r injective, independent third physical mode, U0, endpoint,
H1-C3 or the continuum Yang--Mills mass gap. No model substitution,
Dobrushin, independent Haar posterior, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonAllFineGLMass

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- For EVERY nonnegative fine coupling and EVERY finite Krylov depth,
the actual two-interacting-Wilson-posterior GL mass vanishes precisely
on the zero true Gauss-law physical Hilbert source. The historical OQ
quadratic-collapse branch and OR small-fine dichotomy are no longer
needed: OW independently proved the actual all-context GI kernel
faithful to S_r for the entire finite Krylov family. -/
theorem p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg)
    (r : ℕ) (a : Fin (r + 1) → ℝ) :
    Mass (S r a) (Finset.univ : Finset Link) = 0 ↔ S r a = 0 := by
  have hKernel :=
    p4Q2OW_actualPositiveFrozen_allFine_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ r
  exact p4Q2OR_originalAllDepth_mass_zero_iff_physicalZero_of_kernelEquality
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen r a hKernel

/-- STRICT original interacting-two-posterior GI/GL mass positivity
for EVERY genuine physically nonzero finite right-Krylov Wilson source,
at arbitrary nonnegative fine coupling and positive frozen coupling.
This is qualitative finite-volume positivity, not an H-uniform floor. -/
theorem p4Q2OX_originalPositiveFrozen_allFine_allDepth_nonzero_mass_pos
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg)
    (r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSource : S r a ≠ 0) :
    0 < Mass (S r a) (Finset.univ : Finset Link) := by
  have hKernel :=
    p4Q2OW_actualPositiveFrozen_allFine_allDepth_sourceKernel_eq_fullGIKernel
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀ r
  exact p4Q2OR_originalAllDepth_mass_pos_of_kernelEquality
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n hFrozen r a hKernel hSource

end OriginalWilsonAllFineGLMass
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OX_originalPositiveFrozen_allFine_allDepth_massZero_iff_physicalZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OX_originalPositiveFrozen_allFine_allDepth_nonzero_mass_pos
