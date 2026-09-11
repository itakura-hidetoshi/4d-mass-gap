import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureFiniteGram
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance boundaryGramOpenHalfL2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryGramOpenHalfL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryGramOpenHalfL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryGramOpenHalfL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryGramOpenHalfL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryGramOpenHalfL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real `L²` of the actual positive open-half product Haar measure for the
even-periodic `SU(N)` Wilson lattice. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- The reflected-diagonal Gibbs density is integrable on the positive open
half.  Compactness enters only through the finite normalized Haar measure and
the already-proved reciprocal-partition-function bound. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_diagonalDensity_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Integrable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hpair : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x)) :=
    measurable_id.prodMk hc
  have hdiag : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))) :=
    measurable_const.prodMk hpair
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hm : Measurable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal) :=
    (ENNReal.measurable_toReal.comp hd).comp hdiag
  exact Integrable.of_bound hm.aestronglyMeasurable C.base.partitionFunction⁻¹
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      simpa [C] using
        periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_toReal_le_inv_partitionFunction
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x)))

/-- The completed positive Wilson boundary Gram feature is square-integrable on
the positive open half.  Its squared norm is exactly the reflected-diagonal
Gibbs density, so no auxiliary integrability assumption is needed. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_norm_sq_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    Integrable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x‖ ^ 2)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  apply
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_diagonalDensity_integrable
      H N hN beta hbeta b).congr
  filter_upwards with x
  symm
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
        H N hN beta hbeta b x),
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity,
    Real.sq_sqrt ENNReal.toReal_nonneg]

/-- The actual completed positive boundary Gram feature belongs to open-half
Haar `L²`. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_memLp_two
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    MemLp
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b)
      2
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_measurable
      H N hN beta hbeta b).aestronglyMeasurable).2
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_norm_sq_integrable
      H N hN beta hbeta b)

/-- Canonical open-half Haar-`L²` vector represented by one actual completed
positive Wilson boundary Gram feature. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_memLp_two
    H N hN beta hbeta b).toLp
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b)

/-- The squared Hilbert norm of the open-half Gram vector is the integral of the
pointwise squared feature. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta b‖ ^ 2 =
      ∫ x,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x‖ ^ 2
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let v := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
    H N hN beta hbeta b
  calc
    ‖v‖ ^ 2 = inner ℝ v v := by
      simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∫ x, inner ℝ (v x) (v x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
      MeasureTheory.L2.inner_def v v
    _ = ∫ x,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x‖ ^ 2
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards
        [(periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_memLp_two
          H N hN beta hbeta b).coeFn_toLp] with x hx
      rw [show v x =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x by
        exact hx]
      exact real_inner_self_eq_norm_sq _

/-- The open-half Gram-vector norm has the direct physical density expression:
its square is the reflected-diagonal boundary-fibered Gibbs mass. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq_eq_diagonalDensityIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta b‖ ^ 2 =
      ∫ x,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H x))).toReal
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
        H N hN beta hbeta b x),
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity,
    Real.sq_sqrt ENNReal.toReal_nonneg]

/-- The canonical boundary Gram kernel obtained by taking Hilbert inner products
of the actual open-half Wilson Gram vectors. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
      H N hN beta hbeta b)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
      H N hN beta hbeta c)

/-- The actual compact Wilson boundary Gram kernel has a real Hilbert feature
realization on open-half Haar `L²`. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramL2KernelFeature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
      (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta) where
  FeatureHilbert := PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N
  feature := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
    H N hN beta hbeta
  kernel_eq_inner := by
    intro b c
    rfl

/-- Symmetry of the actual compact Wilson boundary `L²` Gram kernel. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_symmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b c =
      periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta c b :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramL2KernelFeature
    H N hN beta hbeta).symmetric b c

/-- Positive semidefiniteness of the actual compact Wilson boundary `L²` Gram
kernel, for every finite family of boundary configurations and real
coefficients. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_positiveSemidefinite
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefinite
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
      (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta) :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramL2KernelFeature
    H N hN beta hbeta).positiveSemidefinite

end

end MathlibAnalytic
end MGAP4D
