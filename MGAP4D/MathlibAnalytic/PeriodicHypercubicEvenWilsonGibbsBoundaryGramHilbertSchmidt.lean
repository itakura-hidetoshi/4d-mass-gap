import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfProductL2
import Mathlib.MeasureTheory.Integral.Prod
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

/-- Product Haar measure on two copies of the actual shared boundary.  This is
    the natural carrier measure for the compact Wilson boundary Gram kernel. -/
noncomputable def periodicHypercubicEvenBoundaryPairHaarMeasure
    (H N : ℕ) : Measure
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :=
  (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
    (periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- The actual compact Wilson boundary Gram kernel is jointly measurable in
    its two shared-boundary variables.  The proof uses the concrete
    open-half Haar integral formula rather than the `Lp` quotient. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_jointMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2) := by
  let Boundary := PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N
  let Half := PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  letI : SFinite mu := by
    dsimp [mu, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  let g := fun p : Boundary × Half =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2
  have hg : Measurable g := by
    simpa [g, Boundary, Half] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
        H N hN beta hbeta
  have hleft : Measurable
      (fun p : (Boundary × Boundary) × Half => g (p.1.1, p.2)) := by
    exact hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hright : Measurable
      (fun p : (Boundary × Boundary) × Half => g (p.1.2, p.2)) := by
    exact hg.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hint : StronglyMeasurable
      (fun p : Boundary × Boundary =>
        ∫ x, g (p.1, x) * g (p.2, x) ∂mu) :=
    (hleft.mul hright).stronglyMeasurable.integral_prod_right'
  have heq :
      (fun p : Boundary × Boundary =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2) =
      (fun p : Boundary × Boundary =>
        ∫ x, g (p.1, x) * g (p.2, x) ∂mu) := by
    funext p
    simpa [g, mu, Boundary, Half] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_mul
        H N hN beta hbeta p.1 p.2
  rw [heq]
  exact hint.measurable

/-- Uniform absolute bound on the actual boundary Gram kernel by the reciprocal
    finite-volume partition function.  This is volume-finite and sufficient
    for the Hilbert--Schmidt `L²(boundary × boundary)` construction below. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_abs_le_inv_partitionFunction
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    |periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta b c| ≤
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction⁻¹ := by
  let mu := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let zinv : ℝ := C.base.partitionFunction⁻¹
  let M : ℝ := Real.sqrt zinv
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hzinv : 0 ≤ zinv := le_of_lt (inv_pos.mpr hZ)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = zinv := by
    exact Real.sq_sqrt hzinv
  have hpoint : ∀ x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x *
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta c x‖ ≤ zinv := by
    intro x
    let gb := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x
    let gc := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta c x
    have hgb0 : 0 ≤ gb :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
        H N hN beta hbeta b x
    have hgc0 : 0 ≤ gc :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
        H N hN beta hbeta c x
    have hgb : gb ≤ M := by
      simpa [gb, M, zinv, C] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
          H N hN beta hbeta b x
    have hgc : gc ≤ M := by
      simpa [gc, M, zinv, C] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
          H N hN beta hbeta c x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgb0 hgc0)]
    nlinarith [hMsq]
  have hnorm :=
    norm_integral_le_of_norm_le_const
      (μ := mu) (f := fun x =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x *
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta c x)
      (Filter.Eventually.of_forall hpoint)
  have hmass : mu.real Set.univ = 1 := by simp
  rw [hmass, mul_one] at hnorm
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_eq_integral_mul]
  simpa [Real.norm_eq_abs, zinv, C, mu] using hnorm

/-- The squared norm of the actual boundary Gram kernel is integrable on the
    boundary-pair Haar measure. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_norm_sq_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2)
      (periodicHypercubicEvenBoundaryPairHaarMeasure H N) := by
  let pairMeasure := periodicHypercubicEvenBoundaryPairHaarMeasure H N
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let zinv : ℝ := C.base.partitionFunction⁻¹
  letI : IsFiniteMeasure pairMeasure := by
    dsimp [pairMeasure, periodicHypercubicEvenBoundaryPairHaarMeasure,
      periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  have hZ : 0 < C.base.partitionFunction :=
    compact_oriented_partitionFunction_pos C.base
      (continuous_compact_oriented_boltzmannIntegrable C)
  have hzinv : 0 ≤ zinv := le_of_lt (inv_pos.mpr hZ)
  have hm :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_jointMeasurable
      H N hN beta hbeta
  have hsqMeasurable : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2) :=
    hm.norm.pow_const 2
  exact Integrable.of_bound hsqMeasurable.aestronglyMeasurable (zinv ^ 2)
    (Filter.Eventually.of_forall fun p => by
      let k := periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
        H N hN beta hbeta p.1 p.2
      have hk : |k| ≤ zinv := by
        simpa [k, zinv, C] using
          periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_abs_le_inv_partitionFunction
            H N hN beta hbeta p.1 p.2
      have hk0 : 0 ≤ |k| := abs_nonneg _
      have hsq : |k| ^ 2 ≤ zinv ^ 2 := by nlinarith
      change |‖k‖ ^ 2| ≤ zinv ^ 2
      rw [abs_of_nonneg (sq_nonneg ‖k‖), Real.norm_eq_abs]
      simpa [sq_abs] using hsq)

/-- The actual compact Wilson shared-boundary Gram kernel belongs to
    `L²(boundary Haar × boundary Haar)`. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_memLp_two
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    MemLp
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2)
      2
      (periodicHypercubicEvenBoundaryPairHaarMeasure H N) :=
  (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_jointMeasurable
      H N hN beta hbeta).aestronglyMeasurable).2
    (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_norm_sq_integrable
      H N hN beta hbeta)

/-- Hilbert space of square-integrable kernels on two copies of the actual
    compact Wilson shared boundary. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryPairL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenBoundaryPairHaarMeasure H N)

/-- Canonical Hilbert--Schmidt kernel vector represented by the actual compact
    Wilson shared-boundary Gram kernel. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryPairL2 H N :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_memLp_two
    H N hN beta hbeta).toLp
      (fun p =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2)

/-- The Hilbert--Schmidt square norm is exactly the boundary-pair Haar integral
    of the squared actual Gram kernel. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta‖ ^ 2 =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryPairHaarMeasure H N) := by
  let v :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
      H N hN beta hbeta
  let hv :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_memLp_two
      H N hN beta hbeta
  calc
    ‖v‖ ^ 2 = inner ℝ v v := by
      simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∫ p, inner ℝ (v p) (v p)
        ∂(periodicHypercubicEvenBoundaryPairHaarMeasure H N) :=
      MeasureTheory.L2.inner_def v v
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryPairHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with p hp
      rw [show v p =
          periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
            H N hN beta hbeta p.1 p.2 by exact hp]
      exact real_inner_self_eq_norm_sq _

/-- Audit-visible receipt for the actual compact Wilson Hilbert--Schmidt
    shared-boundary Gram kernel. -/
structure PeriodicHypercubicEvenWilsonGibbsBoundaryGramHilbertSchmidtPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  jointMeasurable :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2)
  pairMemLpTwo :
    MemLp
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta p.1 p.2)
      2
      (periodicHypercubicEvenBoundaryPairHaarMeasure H N)
  pointwiseBound :
    ∀ b c,
      |periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel
          H N hN beta hbeta b c| ≤
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.partitionFunction⁻¹

/-- The current compact Wilson Gram construction supplies the complete
    Hilbert--Schmidt kernel receipt without any additional analytic hypothesis. -/
theorem periodicHypercubicEvenWilsonGibbsBoundaryGramHilbertSchmidtPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonGibbsBoundaryGramHilbertSchmidtPackage
      H N hN beta hbeta :=
  { jointMeasurable :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_jointMeasurable
        H N hN beta hbeta
    pairMemLpTwo :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_pair_memLp_two
        H N hN beta hbeta
    pointwiseBound :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramL2Kernel_abs_le_inv_partitionFunction
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
