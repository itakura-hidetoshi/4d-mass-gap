import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabSourceCrossRatioLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The purely right-boundary spatial half-action factor contributed by updating
one right-boundary link.  Unlike the crossing Wilson factor, this quantity is
independent of the left boundary configuration. -/
def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (-beta * ((1 / 2 : ℝ) *
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p))))

/-- The right-boundary spatial half-update factor is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_pos
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
      H N beta B target g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
  exact Real.exp_pos _

/-- The exact right-update local factor splits into the crossing-kernel
replacement and an `A`-independent right-boundary spatial half-action factor.
The identity is division-free. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_mul_referenceCrossing_eq_crossing_mul_spatialHalfUpdateFactor
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g *
        specialUnitaryWilsonRelativeKernel N beta (A target) (B target) =
      specialUnitaryWilsonRelativeKernel N beta (A target) g *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B target g := by
  simp only [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor,
    specialUnitaryWilsonRelativeKernel,
    specialUnitaryWilsonBoltzmannCentralFunction,
    ← Real.exp_add]
  congr 1
  ring

/-- For two replacement values `h` and `k`, the left-boundary dependence of
their local-factor ratio is exactly the source crossing-kernel ratio; the two
right-boundary spatial factors are independent of `A` and appear as explicit
multiplicative constants. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pairwise_sourceTilt
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h *
        specialUnitaryWilsonRelativeKernel N beta (A target) k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B target k =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target k *
        specialUnitaryWilsonRelativeKernel N beta (A target) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B target h := by
  have hh :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_mul_referenceCrossing_eq_crossing_mul_spatialHalfUpdateFactor
      H N beta A B target h
  have hk :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_mul_referenceCrossing_eq_crossing_mul_spatialHalfUpdateFactor
      H N beta A B target k
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h *
        specialUnitaryWilsonRelativeKernel N beta (A target) k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B target k =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h *
        (specialUnitaryWilsonRelativeKernel N beta (A target) k *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
            H N beta B target k) := by ring
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target k *
          specialUnitaryWilsonRelativeKernel N beta (A target) (B target)) := by
      rw [← hk]
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target k *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target h *
          specialUnitaryWilsonRelativeKernel N beta (A target) (B target)) := by ring
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target k *
        (specialUnitaryWilsonRelativeKernel N beta (A target) h *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
            H N beta B target h) := by
      rw [hh]
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target k *
        specialUnitaryWilsonRelativeKernel N beta (A target) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B target h := by ring

/-- Pointwise source-update factorization for the complete raw one-slab kernel.
After multiplying by the reference crossing kernel, the replacement value
appears only through the source crossing factor and the `A`-independent
right-boundary spatial half-update factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_mul_referenceCrossing_eq
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source h) *
        specialUnitaryWilsonRelativeKernel N beta (A source) (B source) =
      specialUnitaryWilsonRelativeKernel N beta (A source) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_mul_referenceCrossing_eq_crossing_mul_spatialHalfUpdateFactor
      H N beta A B source h
  calc
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) *
      specialUnitaryWilsonRelativeKernel N beta (A source) (B source) =
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B source h *
          specialUnitaryWilsonRelativeKernel N beta (A source) (B source)) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
      ring
    _ = (specialUnitaryWilsonRelativeKernel N beta (A source) h *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
            H N beta B source h) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
      rw [hLocal]
    _ = specialUnitaryWilsonRelativeKernel N beta (A source) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
      ring

/-- Division-free likelihood-ratio identity for two source-conditioned raw
one-slab kernels at one fixed left boundary.  The only `A`-dependent ratio
factor is the one-link Wilson crossing kernel at `source`; the spatial factors
are constants with respect to `A`.

This is the pointwise form needed before passing to a normalized left-boundary
change of measure and a target--source covariance estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_pairwise_likelihoodRatio
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source h) *
        specialUnitaryWilsonRelativeKernel N beta (A source) k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (Function.update B source k) *
        specialUnitaryWilsonRelativeKernel N beta (A source) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h := by
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pairwise_sourceTilt
      H N beta A B source h k
  calc
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) *
      specialUnitaryWilsonRelativeKernel N beta (A source) k *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
        H N beta B source k =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source h *
        specialUnitaryWilsonRelativeKernel N beta (A source) k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
        ring
    _ = (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k *
        specialUnitaryWilsonRelativeKernel N beta (A source) h *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h) *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
        rw [hLocal]
    _ = (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B source k *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B) *
      specialUnitaryWilsonRelativeKernel N beta (A source) h *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
        H N beta B source h := by
        ring

end

end MathlibAnalytic
end MGAP4D
