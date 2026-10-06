import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalUniformFloorSweepScaling
import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Tactic

/-!
# Generator scaling for the volume-uniform posterior full-sweep factor

PRs #5200--#5201 produce the actual canonical posterior full-sweep contraction

  rho(s,beta) = exp(-(1 - alpha_bar(s,beta))),

with alpha_bar independent of H and N, and show that a fixed rho < 1 driven for
floor(t / a_n) sweeps decays to zero as a_n -> 0.

A finite nonzero continuum mass requires a finer scaling statement: the
per-sweep logarithmic gap must itself be of order the lattice spacing. Since

  -log rho(s,beta) = 1 - alpha_bar(s,beta),

the exact derived mass rate is

  m_n = (1 - alpha_bar(s,beta_n)) / a_n.

This file packages the missing generator-scaling hypothesis as a proof-relevant
certificate and connects it directly to the existing positive discrete
transfer-rate limit infrastructure. Under

  (1 - alpha_bar(s,beta_n)) / a_n -> m > 0,

the genuine floor-selected posterior full-sweep powers satisfy

  rho(s,beta_n) ^ floor(t / a_n) -> exp(-m t).

The final theorem transfers this scalar rate to any varying finite-volume
posterior variation trajectory whose floor-sweep values have a real limit.

This is a conditional generator-scaling bridge. It does not prove from Wilson
couplings alone that the displayed gap-rate limit exists, and it does not
identify posterior random-scan sweeps with the Euclidean transfer operator.
Those remain separate analytic and physical obligations.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology BigOperators

noncomputable section

local instance posteriorFullSweepGeneratorScalingSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The negative logarithm of the canonical posterior full-sweep factor is
exactly the H-independent Dobrushin gap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_neg_log_eq_gap
    (s beta : ℝ) :
    -Real.log
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s beta) =
      1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
  rw [Real.log_exp]
  ring

/-- The derived mass rate of the actual canonical full-sweep factor is exactly
the Dobrushin gap divided by lattice spacing. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_massRate_eq_gap_div_spacing
    (s beta spacing : ℝ) :
    -Real.log
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s beta) /
        spacing =
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta) /
        spacing := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_neg_log_eq_gap]

/-- Proof-relevant scaling certificate asserting that the exact posterior
full-sweep logarithmic gap has a finite positive spacing-scaled limit. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
    (s : ℝ)
    (hs : 8 < s)
    (latticeSpacing beta : ℕ → ℝ) where
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero :
    Tendsto latticeSpacing atTop (nhds 0)
  beta_nonneg : ∀ n, 0 ≤ beta n
  beta_le_cutoff :
    ∀ n,
      beta n ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs
  mass : ℝ
  mass_pos : 0 < mass
  gapRate_tendsto :
    Tendsto
      (fun n =>
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s (beta n)) /
          latticeSpacing n)
      atTop (nhds mass)

namespace
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

variable
    {s : ℝ}
    {hs : 8 < s}
    {latticeSpacing beta : ℕ → ℝ}

/-- The actual canonical posterior full-sweep factors form a positive discrete
transfer-rate limit under the generator-scaling certificate. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    PositiveDiscreteTransferRateLimit
      latticeSpacing
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s (beta n)) := by
  refine
    { latticeSpacing_pos := A.latticeSpacing_pos
      latticeSpacing_tendsto_zero := A.latticeSpacing_tendsto_zero
      transferFactor_pos := ?_
      transferFactor_le_one := ?_
      mass := A.mass
      mass_pos := A.mass_pos
      massRate_tendsto := ?_ }
  · intro n
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_pos
        s (beta n)
  · intro n
    exact le_of_lt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_lt_one
        s hs (beta n) (A.beta_nonneg n) (A.beta_le_cutoff n))
  · simpa only [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_massRate_eq_gap_div_spacing
    ] using A.gapRate_tendsto

/-- The derived mass rate exposed by the generic transfer-rate certificate is
literally the spacing-scaled posterior Dobrushin gap. -/
theorem massRate_eq_gap_div_spacing
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (n : ℕ) :
    A.toPositiveDiscreteTransferRateLimit.massRate n =
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s (beta n)) /
        latticeSpacing n := by
  unfold PositiveDiscreteTransferRateLimit.massRate
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_massRate_eq_gap_div_spacing
      s (beta n) (latticeSpacing n)

/-- Floor-selected powers of the actual posterior full-sweep factor converge to
the continuum exponential generated by the spacing-scaled Dobrushin-gap limit. -/
theorem floorFullSweepRatePow_tendsto
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s (beta n)) ^
          physicalTemporalFloorNatStep latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  exact
    A.toPositiveDiscreteTransferRateLimit.floorPow_tendsto t

/-- Varying finite-volume posterior variation data with one common scalar
envelope.  Bundling these fields keeps downstream theorem interfaces short and
makes the volume-uniform content explicit. -/
structure FloorSweepVariationFamily where
  N : ℕ
  hN : 0 < N
  H : ℕ → ℕ
  boundary :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H n) N
  variation :
    (n : ℕ) →
      PeriodicHypercubicEvenSpatialSliceLink (H n) → ℝ
  variation_nonneg : ∀ n e, 0 ≤ variation n e
  envelope : ℝ
  envelope_nonneg : 0 ≤ envelope
  variation_le : ∀ n e, variation n e ≤ envelope
  source :
    (n : ℕ) → PeriodicHypercubicEvenSpatialSliceLink (H n)

/-- Scalar variation value after the floor-selected number of complete sweeps
at scale n. -/
noncomputable def floorSweepVariationValue
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (F : FloorSweepVariationFamily)
    (t : NNReal)
    (n : ℕ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      (F.H n) F.N F.hN s hs (beta n) (A.beta_nonneg n)
      (A.beta_le_cutoff n) (F.boundary n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
    (F.variation n)
    (physicalTemporalFloorNatStep latticeSpacing t n *
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (F.H n)))
    (F.source n)

/-- Pointwise floor-sweep variation bound along arbitrary varying finite
volumes, with the coupling allowed to vary according to the scaling
certificate. -/
theorem floorSweepVariationValue_le
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (F : FloorSweepVariationFamily)
    (t : NNReal)
    (n : ℕ) :
    A.floorSweepVariationValue F t n ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s (beta n)) ^
          physicalTemporalFloorNatStep latticeSpacing t n *
        F.envelope := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_fullSweep_le
      (F.H n) F.N F.hN s hs
      (beta n) (A.beta_nonneg n) (A.beta_le_cutoff n)
      (F.boundary n)
      (F.variation n) (F.variation_nonneg n)
      F.envelope F.envelope_nonneg (F.variation_le n)
      (physicalTemporalFloorNatStep latticeSpacing t n)
      (F.source n)

/-- If the varying finite-volume floor-sweep posterior variation has a real
limit, that limit is bounded by the continuum exponential generated by the
spacing-scaled Dobrushin gap. -/
theorem floorSweepVariationValue_limit_le
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (F : FloorSweepVariationFamily)
    (t : NNReal)
    (limit : ℝ)
    (hLimit :
      Tendsto (A.floorSweepVariationValue F t) atTop (nhds limit)) :
    limit ≤ Real.exp (-A.mass * (t : ℝ)) * F.envelope := by
  apply le_of_tendsto_of_tendsto hLimit
    ((A.floorFullSweepRatePow_tendsto t).mul_const F.envelope)
  exact Filter.Eventually.of_forall fun n =>
    A.floorSweepVariationValue_le F t n

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
