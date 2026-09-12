import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtOperatorSymmetric
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfProductL2
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtGramPositiveKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The physical scalar Wilson Gram kernel is represented by the open-half
integral of products of the shared completed positive Gram feature. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_integralGram
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealL2KernelRepresentativeIntegralGram
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2)
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2) := by
  intro p
  exact
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_mul
      H N hN beta hbeta p.1 p.2

/-- For every complete boundary-Haar `L²` vector, the natural three-variable
weighted Wilson Gram product is integrable.  Compact Haar probability
normalization converts the two boundary `L²` representatives to `L¹`, while
the physical Gram feature is uniformly bounded by `sqrt (Z⁻¹)`. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_weightedTriple_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    Integrable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta q.1.1 q.2 * f q.1.1) *
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta q.1.2 q.2 * f q.1.2))
      (((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenBoundaryHaarMeasure H N)).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let C := Real.sqrt
    (((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction)⁻¹)
  letI : IsProbabilityMeasure boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : IsProbabilityMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hf1 : Integrable (fun b => f b) boundaryMeasure := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hpair : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        ‖f p.1‖ * ‖f p.2‖)
      (boundaryMeasure.prod boundaryMeasure) := by
    simpa [smul_eq_mul] using hf1.norm.smul_prod hf1.norm
  have hdomPair : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        C ^ 2 * (‖f p.1‖ * ‖f p.2‖))
      (boundaryMeasure.prod boundaryMeasure) := by
    exact hpair.const_mul (C ^ 2)
  have hdom : Integrable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        C ^ 2 * (‖f q.1.1‖ * ‖f q.1.2‖))
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) := by
    exact hdomPair.comp_fst halfMeasure
  have hphi :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta
  have hleftMap : Measurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hrightMap : Measurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (q.1.2, q.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hphiLeft : AEStronglyMeasurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta q.1.1 q.2)
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) :=
    (hphi.comp hleftMap).aestronglyMeasurable
  have hphiRight : AEStronglyMeasurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta q.1.2 q.2)
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) :=
    (hphi.comp hrightMap).aestronglyMeasurable
  have hfLeftPair : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        f p.1)
      (boundaryMeasure.prod boundaryMeasure) :=
    (Lp.aestronglyMeasurable f).comp_fst
  have hfRightPair : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        f p.2)
      (boundaryMeasure.prod boundaryMeasure) :=
    (Lp.aestronglyMeasurable f).comp_snd
  have hfLeft : AEStronglyMeasurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        f q.1.1)
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) :=
    hfLeftPair.comp_fst
  have hfRight : AEStronglyMeasurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        f q.1.2)
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) :=
    hfRightPair.comp_fst
  have hmeas : AEStronglyMeasurable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta q.1.1 q.2 * f q.1.1) *
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta q.1.2 q.2 * f q.1.2))
      ((boundaryMeasure.prod boundaryMeasure).prod halfMeasure) :=
    (hphiLeft.mul hfLeft).mul (hphiRight.mul hfRight)
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  apply hdom.mono' hmeas
  filter_upwards with q
  let phi1 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta q.1.1 q.2
  let phi2 := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta q.1.2 q.2
  have hphi10 : 0 ≤ phi1 := by
    dsimp [phi1]
    exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta q.1.1 q.2
  have hphi20 : 0 ≤ phi2 := by
    dsimp [phi2]
    exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta q.1.2 q.2
  have hphi1 : ‖phi1‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg hphi10]
    dsimp [phi1, C]
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
        H N hN beta hbeta q.1.1 q.2
  have hphi2 : ‖phi2‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg hphi20]
    dsimp [phi2, C]
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
        H N hN beta hbeta q.1.2 q.2
  have hbound :
      ‖(phi1 * f q.1.1) * (phi2 * f q.1.2)‖ ≤
        C ^ 2 * (‖f q.1.1‖ * ‖f q.1.2‖) := by
    rw [norm_mul, norm_mul, norm_mul]
    calc
      (‖phi1‖ * ‖f q.1.1‖) * (‖phi2‖ * ‖f q.1.2‖) =
          (‖phi1‖ * ‖phi2‖) * (‖f q.1.1‖ * ‖f q.1.2‖) := by ring
      _ ≤ (C * C) * (‖f q.1.1‖ * ‖f q.1.2‖) := by
        gcongr
      _ = C ^ 2 * (‖f q.1.1‖ * ‖f q.1.2‖) := by ring
  have hdom0 : 0 ≤ C ^ 2 * (‖f q.1.1‖ * ‖f q.1.2‖) := by positivity
  simpa [phi1, phi2, Real.norm_eq_abs, abs_of_nonneg hdom0] using hbound

/-- Exact complete-boundary quadratic-form identity for the actual compact
Wilson Gram operator kernel: the double boundary integral is the open-half
integral of the square of the analyzed boundary amplitude. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_integral_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
          H N hN beta hbeta) f f =
      ∫ x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
        (∫ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta b x * f b
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) ^ 2
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  exact
    realL2HilbertSchmidtKernelPairing_self_eq_integral_sq_of_ae_integralGram_rep
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta p.1 p.2)
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2)
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_coeFn
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_integralGram
        H N hN beta hbeta)
      f
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_weightedTriple_integrable
        H N hN beta hbeta f)

/-- The actual compact Wilson Hilbert--Schmidt kernel pairing is nonnegative on
the full boundary Haar `L²` space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_nonnegative
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingNonnegative
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta) := by
  intro f
  rw [periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_integral_sq
    H N hN beta hbeta f]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)

/-- The actual compact Wilson shared-boundary Hilbert--Schmidt operator is
positive on the complete boundary Haar `L²` Hilbert space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_isPositive
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsPositive := by
  exact realL2HilbertSchmidtKernelOperator_isPositive
    (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta)
    (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
      H N hN beta hbeta)
    (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_nonnegative
      H N hN beta hbeta)

/-- Audit-visible actual Wilson complete-`L²` Gram positivity package. -/
structure PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPositivePackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  pairingSymmetric :
    RealL2HilbertSchmidtKernelPairingSymmetric
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
  pairingNonnegative :
    RealL2HilbertSchmidtKernelPairingNonnegative
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
  operatorPositive :
    ((periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsPositive
  quadraticIdentity :
    ∀ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N),
      realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
            H N hN beta hbeta) f f =
        ∫ x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
          (∫ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta b x * f b
            ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) ^ 2
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- Construct the actual Wilson complete-`L²` Gram positivity receipt. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPositivePackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPositivePackage
      H N hN beta hbeta :=
  { pairingSymmetric :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
        H N hN beta hbeta
    pairingNonnegative :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_nonnegative
        H N hN beta hbeta
    operatorPositive :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_isPositive
        H N hN beta hbeta
    quadraticIdentity :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_integral_sq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
