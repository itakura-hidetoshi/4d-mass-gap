import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingDobrushinGibbsBoundaryL2TransferGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2PoincareGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorParallelHeatBathBlockL2
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The canonical eight-color Gibbs residual seen from the shared-boundary
carrier through the already existing typed `boundaryAnalysis` map.

The formula is kept at the low-level eight-color block layer so this bridge does
not import the physical one-slab bounded-color reduction back into the higher
Gibbs-boundary certificate hierarchy.  It is the same fixed-color-count
normalization: the inverse cardinality of the canonical eight-color type times
the sum of squared block residuals.

No carrier identification is made here: the input is a boundary-Haar `L²`
vector, `boundaryAnalysis` sends it to the global finite Wilson Gibbs `L²`
carrier, and only there is the eight-color residual evaluated. -/
noncomputable def boundaryAnalyzedEightColorResidualEnergy
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) : ℝ :=
  let f := Q.boundaryAnalysis n t v
  ((Fintype.card PeriodicHypercubicEvenEdgeColor : ℝ)⁻¹) *
    ∑ color : PeriodicHypercubicEvenEdgeColor,
      ‖f -
        periodicHypercubicEvenSpecialUnitaryEightColorHeatBathBlockL2
          (halfExtent n) N hN (beta n) (hbeta n) color f‖ ^ 2

/-- The boundary-analyzed eight-color residual is nonnegative because it is a
fixed positive normalization of a finite sum of squared Gibbs-`L²` block
residuals. -/
theorem boundaryAnalyzedEightColorResidualEnergy_nonneg
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    0 ≤ Q.boundaryAnalyzedEightColorResidualEnergy n t v := by
  unfold boundaryAnalyzedEightColorResidualEnergy
  positivity

/-- The literal squared-norm defect of the already existing typed
analysis/evolution/synthesis boundary transfer. -/
noncomputable def factorizedBoundarySquaredDefect
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) : ℝ :=
  ‖v‖ ^ 2 -
    ‖(Q.boundarySynthesis n t).comp
        ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t)) v‖ ^ 2

/-- Time-dependent bounded-color reduction on the actual typed boundary/Gibbs
bridge.

The two model-facing obligations are deliberately separated:

* `hframe` compares the boundary norm with the canonical eight-color residual
  of its explicitly analyzed Gibbs vector;
* `hcompare` compares that Gibbs residual with the literal squared defect of
  the factorized shared-boundary transfer.

Their product `eta(t) * kappa(t)` is therefore a genuine boundary `L²`
Poincare defect factor.  Allowing both factors to depend on `t` preserves the
small-time slope required by the existing continuum gap route. -/
theorem boundaryPoincareDefect_of_eightColorResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (kappa eta : NNReal → ℝ)
    (heta0 : ∀ t, 0 ≤ eta t)
    (hframe : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      kappa t * ‖v‖ ^ 2 ≤ Q.boundaryAnalyzedEightColorResidualEnergy n t v)
    (hcompare : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      eta t * Q.boundaryAnalyzedEightColorResidualEnergy n t v ≤
        Q.factorizedBoundarySquaredDefect n t v)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    (eta t * kappa t) * ‖v‖ ^ 2 ≤
      Q.factorizedBoundarySquaredDefect n t v := by
  have hscaled := mul_le_mul_of_nonneg_left (hframe n t v) (heta0 t)
  calc
    (eta t * kappa t) * ‖v‖ ^ 2 =
        eta t * (kappa t * ‖v‖ ^ 2) := by ring
    _ ≤ eta t * Q.boundaryAnalyzedEightColorResidualEnergy n t v := hscaled
    _ ≤ Q.factorizedBoundarySquaredDefect n t v := hcompare n t v

/-- Convert a time-dependent eight-color Gibbs residual estimate on the typed
boundary-analysis image directly into the repository's existing shared-boundary
`L²` Poincare certificate.

This is the carrier-safe bridge needed by the downstream OS/continuum route.
It does not assert `hframe` or `hcompare`; those remain the two concrete Wilson
model obligations.  It also does not identify global Gibbs `L²`, boundary Haar
`L²`, spatial Haar `L²`, or the Gauss-law physical Hilbert carrier. -/
noncomputable def toApproximatingBoundaryL2PoincareGapCertificate_of_eightColorResidual
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (mass : ℝ)
    (hmass : 0 < mass)
    (kappa eta : NNReal → ℝ)
    (hkappa0 : ∀ t, 0 ≤ kappa t)
    (heta0 : ∀ t, 0 ≤ eta t)
    (hetaKappa_le_one : ∀ t, eta t * kappa t ≤ 1)
    (hslope :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ *
            (1 - Real.sqrt (1 - eta (t + t) * kappa (t + t))))
        (nhdsWithin 0 (Ioi 0))
        (nhds mass))
    (hframe : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      kappa t * ‖v‖ ^ 2 ≤ Q.boundaryAnalyzedEightColorResidualEnergy n t v)
    (hcompare : ∀ (n : ℕ) (t : NNReal)
      (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N),
      eta t * Q.boundaryAnalyzedEightColorResidualEnergy n t v ≤
        Q.factorizedBoundarySquaredDefect n t v) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2PoincareGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := mass
  mass_pos := hmass
  defectFactor := fun t => eta t * kappa t
  defectFactor_nonneg := fun t => mul_nonneg (heta0 t) (hkappa0 t)
  defectFactor_le_one := hetaKappa_le_one
  slope_tendsto := hslope
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := fun n t =>
    (Q.boundarySynthesis n t).comp
      ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t))
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_defect_bound := by
    intro n t v
    exact
      Q.boundaryPoincareDefect_of_eightColorResidual
        kappa eta heta0 hframe hcompare n t v

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
