import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwoSidedOneLinkConditionalExpectation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# Endpoint-swap symmetry of the physical ground-state joint law

The genuine one-slab ground-state density is

  lambda^-1 * Omega(A) * K(A,B) * Omega(B).

The one-slab kernel is symmetric, while the product Haar reference measure is
preserved by exchanging the two boundary configurations.  Hence the genuine
joint probability law itself is invariant under `Prod.swap`.

This is the transport surface needed to reuse the already-developed right
one-link conditional machinery for the left boundary.  No cross-boundary
influence estimate, conditional-expectation conjugacy, or new coupling
coefficient is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance groundStateJointSwapSymmetrySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointSwapSymmetrySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointSwapSymmetrySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointSwapSymmetrySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointSwapSymmetrySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointSwapSymmetrySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The normalized physical ground-state density is pointwise invariant under
exchanging the two slab endpoints. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z.swap =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta z.2 z.1]
  ring

/-- The genuine physical ground-state joint probability measure is invariant
under exchanging its left and right boundary configurations. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measure.map Prod.swap
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN beta hbeta z)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_swap hs]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
  rw [withDensity_apply _ (measurable_swap hs), withDensity_apply _ hs]
  change
    (∫⁻ z in Prod.swap ⁻¹' s, w z ∂μ.prod μ) =
      ∫⁻ z in s, w z ∂μ.prod μ
  calc
    (∫⁻ z in Prod.swap ⁻¹' s, w z ∂μ.prod μ) =
        ∫⁻ z in Prod.swap ⁻¹' s, w z.swap ∂μ.prod μ := by
      apply setLIntegral_congr_fun (measurable_swap hs)
      intro z hz
      dsimp [w]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_swap
          H N hN beta hbeta z]
    _ = ∫⁻ z in s, w z ∂μ.prod μ := by
      exact
        (Measure.measurePreserving_swap (μ := μ) (ν := μ)).setLIntegral_comp_preimage_emb
          MeasurableEquiv.prodComm.measurableEmbedding w s

/-- Endpoint swap is therefore a measure-preserving involution of the genuine
physical ground-state joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MeasurePreserving Prod.swap
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  exact ⟨measurable_swap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_swap
      H N hN beta hbeta⟩

/-- Consequently every nonnegative joint integral is unchanged by exchanging
the two endpoints.  No measurability premise on the integrand is needed because
the swap is a measurable embedding. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_lintegral_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞) :
    (∫⁻ z, Phi z.swap
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) =
      ∫⁻ z, Phi z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta).lintegral_comp_emb
        MeasurableEquiv.prodComm.measurableEmbedding Phi

end

end MathlibAnalytic
end MGAP4D
