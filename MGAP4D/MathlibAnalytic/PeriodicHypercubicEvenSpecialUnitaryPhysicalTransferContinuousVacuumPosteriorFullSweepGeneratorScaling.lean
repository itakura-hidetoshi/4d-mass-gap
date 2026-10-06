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

/-- Pointwise floor-sweep variation bound along arbitrary varying finite
volumes, with the coupling allowed to vary according to the scaling
certificate. -/
theorem floorSweepVariation_le
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    (B :
      (n : ℕ) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H n) N)
    (variation :
      (n : ℕ) →
        PeriodicHypercubicEvenSpatialSliceLink (H n) → ℝ)
    (hVariationNonneg :
      ∀ n e, 0 ≤ variation n e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ n e, variation n e ≤ V)
    (source :
      (n : ℕ) → PeriodicHypercubicEvenSpatialSliceLink (H n))
    (t : NNReal)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          (H n) N hN s hs (beta n) (A.beta_nonneg n) (A.beta_le_cutoff n) (B n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        (variation n)
        (physicalTemporalFloorNatStep latticeSpacing t n *
          Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (H n)))
        (source n) ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s (beta n)) ^
          physicalTemporalFloorNatStep latticeSpacing t n *
        V := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_fullSweep_le
      (H n) N hN s hs
      (beta n) (A.beta_nonneg n) (A.beta_le_cutoff n)
      (B n)
      (variation n) (hVariationNonneg n)
      V hV (hVariationLe n)
      (physicalTemporalFloorNatStep latticeSpacing t n)
      (source n)

/-- If the varying finite-volume floor-sweep posterior variation has a real
limit, that limit is bounded by the continuum exponential generated by the
spacing-scaled Dobrushin gap. -/
theorem floorSweepVariation_limit_le
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta)
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    (B :
      (n : ℕ) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H n) N)
    (variation :
      (n : ℕ) →
        PeriodicHypercubicEvenSpatialSliceLink (H n) → ℝ)
    (hVariationNonneg :
      ∀ n e, 0 ≤ variation n e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ n e, variation n e ≤ V)
    (source :
      (n : ℕ) → PeriodicHypercubicEvenSpatialSliceLink (H n))
    (t : NNReal)
    (limit : ℝ)
    (hLimit :
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
              (H n) N hN s hs (beta n) (A.beta_nonneg n) (A.beta_le_cutoff n) (B n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            (variation n)
            (physicalTemporalFloorNatStep latticeSpacing t n *
              Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (H n)))
            (source n))
        atTop (nhds limit)) :
    limit ≤ Real.exp (-A.mass * (t : ℝ)) * V := by
  apply le_of_tendsto_of_tendsto hLimit
    ((A.floorFullSweepRatePow_tendsto t).mul_const V)
  exact Filter.Eventually.of_forall fun n =>
    A.floorSweepVariation_le
      H N hN B variation hVariationNonneg V hV hVariationLe source t n

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
