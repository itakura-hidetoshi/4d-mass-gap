import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryGramOpenHalfL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance boundaryGramL2KernelIntegralSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryGramL2KernelIntegralSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryGramL2KernelIntegralSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryGramL2KernelIntegralSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryGramL2KernelIntegralSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryGramL2KernelIntegralSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The compact Wilson boundary Hilbert kernel constructed from open-half
Haar-`L²` vectors is literally the integral of the pointwise real Hilbert inner
products of the completed positive Gram features.  This removes the `Lp`
quotient from the kernel formula used by the downstream integral-operator
construction. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b c =
      ∫ x,
        inner ℝ
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x)
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta c x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let hb :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_memLp_two
      H N hN beta hbeta b
  let hc :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_memLp_two
      H N hN beta hbeta c
  let vb := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
    H N hN beta hbeta b
  let vc := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
    H N hN beta hbeta c
  change inner ℝ vb vc = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp, hc.coeFn_toLp] with x hbx hcx
  rw [show vb x =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x by exact hbx]
  rw [show vc x =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta c x by exact hcx]

/-- Scalar form of the preceding kernel identity: the actual compact Wilson
boundary kernel is the open-half Haar integral of the product of its two
completed positive Gram amplitudes. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_mul
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b c =
      ∫ x,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta c x
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_inner]
  apply integral_congr_ae
  filter_upwards with x
  exact periodicHypercubicEven_real_inner_eq_mul _ _

/-- Cauchy--Schwarz control of the actual compact Wilson boundary Gram kernel.
This is the operator-theoretic estimate needed before integrating the kernel in
one boundary variable. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_abs_le_norm_mul_norm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    |periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b c| ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta b‖ *
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta c‖ := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
  exact abs_real_inner_le_norm _ _

/-- On the diagonal, the boundary `L²` Gram kernel is exactly the reflected
boundary-fibered Gibbs mass of the open positive half. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_diagonal_eq_densityIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b b =
      ∫ x,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
  rw [real_inner_self_eq_norm_sq]
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq_eq_diagonalDensityIntegral
      H N hN beta hbeta b

/-- Nonnegativity of the diagonal compact Wilson boundary Gram kernel, now as a
property of the integral kernel rather than merely its abstract Hilbert feature
certificate. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_diagonal_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    0 ≤ periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
      H N hN beta hbeta b b := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
  exact real_inner_self_nonneg

end

end MathlibAnalytic
end MGAP4D