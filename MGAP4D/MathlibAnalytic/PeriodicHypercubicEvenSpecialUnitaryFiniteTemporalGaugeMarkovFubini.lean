import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealizableActualSynthesisRawPathGram
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteTemporalGaugeMarkovFubiniTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteTemporalGaugeMarkovFubiniCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteTemporalGaugeMarkovFubiniSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteTemporalGaugeMarkovFubiniMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteTemporalGaugeMarkovFubiniBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteTemporalGaugeMarkovFubiniSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance finiteTemporalGaugeMarkovFubiniBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance finiteTemporalGaugeMarkovFubiniOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The rectangular completed Gram pairing is already the literal finite Wilson
path integral once the canonical `L²` representatives are exposed.  This is
the scalar entry point for the subsequent temporal-gauge/Fubini decomposition:
no abstract OS transfer, completion, or spectral hypothesis occurs here. -/
theorem periodicHypercubicEvenWilsonBoundaryGramPairing_eq_rawPath_integral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f u =
      ∫ p : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
        periodicHypercubicEvenWilsonBoundaryGramRawPathRectangularKernel
            H N hN beta hbeta p *
          (f p.1 * u p.2)
        ∂((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hK :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn_eq_rawPath
      H N hN beta hbeta
  have hTensor :=
    realL2ExternalTensor_coeFn
      (μ := periodicHypercubicEvenBoundaryHaarMeasure H N)
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H N) f u
  filter_upwards [hK, hTensor] with p hpK hpTensor
  rw [hpK, hpTensor]
  simp [realL2ExternalTensorFunction, realL2Scalar_inner_eq_mul]

end

end MathlibAnalytic
end MGAP4D
