import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumTopRayUniqueness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorLinear
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# One-slab physical transfer beta-Lipschitz compatibility API

The canonical finite-volume beta-Lipschitz implementation now lives in

  PeriodicHypercubicEvenSpecialUnitaryOneSlabKernelBetaLipschitz

and

  PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz.

Historically this file independently reproved the same derivative and
operator-norm theorems under the same fully qualified names.  That is harmless
while either import route is used alone, but Lean merges the environments of
transitively imported modules.  A downstream file importing both routes then
fails because the environment would contain the same declaration name twice.

This file is therefore kept as a compatibility shim:

* the original imports are retained so downstream transitive import behavior is
  not silently narrowed;
* the canonical declarations are re-exported by importing the canonical module;
* only the two legacy theorem names carrying an extra `_beta` suffix are
  retained here as aliases.

No duplicate fully qualified declaration is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology

noncomputable section

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance oneSlabOperatorNormBetaLipschitzSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance oneSlabOperatorNormBetaLipschitzSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Backward-compatible alias for the canonical pointwise one-slab kernel
beta-Lipschitz estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N gamma A B -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_norm_sub_le
      H N hN beta gamma hbeta hgamma A B

/-- Backward-compatible alias for the canonical product-Haar L² one-slab
kernel beta-Lipschitz estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le_beta
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        ‖gamma - beta‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_norm_sub_le
      H N hN beta gamma hbeta hgamma

end

end MathlibAnalytic
end MGAP4D
