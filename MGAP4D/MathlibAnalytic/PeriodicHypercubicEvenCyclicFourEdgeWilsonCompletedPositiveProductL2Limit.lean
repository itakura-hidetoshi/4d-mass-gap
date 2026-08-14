import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonAnalysisProductLimit
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorContinuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgeWilsonProductL2LimitTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeWilsonProductL2LimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonProductL2LimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonProductL2LimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonProductL2LimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonProductL2LimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonProductL2LimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance cyclicFourEdgeWilsonProductL2LimitBoundaryHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFourEdgeWilsonProductL2LimitOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance cyclicFourEdgeWilsonProductL2LimitProductHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryOpenHalfHaarMeasure]
  infer_instance

/-- Every finite four-edge Taylor/Fock approximation to the completed-positive
Wilson boundary kernel lies in product-Haar `L²`.  The estimate uses the
existing degree-independent finite-kernel bound and no scalar probe. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_product_memLp_two
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    MemLp
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2)
      2
      (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
  let C := periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
    H beta hbeta
  have hm :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_jointMeasurable
      hH beta hbeta degree
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  exact Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    (Filter.Eventually.of_forall fun p => by
      let a := periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree p.1 p.2
      have ha : ‖a‖ ≤ C := by
        dsimp [a, C]
        simpa [Real.norm_eq_abs] using
          periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
            H beta hbeta degree p.1 p.2
      change |‖a‖ ^ 2| ≤ C ^ 2
      rw [abs_of_nonneg (sq_nonneg ‖a‖)]
      exact pow_le_pow_left₀ (norm_nonneg a) ha 2)

/-- Canonical product-Haar `L²` vector represented by the complete finite
four-edge Wilson Taylor/Fock kernel. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryOpenHalfL2 H 2 :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_product_memLp_two
    hH beta hbeta degree).toLp
      (fun p =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2)

/-- The product-`L²` norm of the finite kernel is its exact integrated square. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2_norm_sq
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
        H hH beta hbeta degree‖ ^ 2 =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
  let v :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
      H hH beta hbeta degree
  let hv :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_product_memLp_two
      hH beta hbeta degree
  calc
    ‖v‖ ^ 2 = inner ℝ v v := by
      simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∫ p, inner ℝ (v p) (v p)
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) :=
      MeasureTheory.L2.inner_def v v
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with p hp
      rw [show v p =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
            H beta hbeta degree p.1 p.2 by exact hp]
      exact real_inner_self_eq_norm_sq _

/-- Exact square-norm identity for the difference between a finite kernel and
the completed actual Wilson product-`L²` kernel. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2_sub_actual_norm_sq
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
          H hH beta hbeta degree -
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta‖ ^ 2 =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
              H beta hbeta degree p.1 p.2 -
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
  let partialRaw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
      H beta hbeta degree p.1 p.2
  let actualRaw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
      beta hbeta p.1 p.2
  let hp :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_product_memLp_two
      hH beta hbeta degree
  let ha :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta
  let d := (hp.sub ha).toLp (partialRaw - actualRaw)
  have hd :
      d =
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
            H hH beta hbeta degree -
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
            H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta := by
    dsimp [d, hp, ha, partialRaw, actualRaw,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2]
    exact
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_product_memLp_two
          hH beta hbeta degree).toLp_sub
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)
  rw [← hd]
  calc
    ‖d‖ ^ 2 = inner ℝ d d := by
      simpa using (real_inner_self_eq_norm_sq d).symm
    _ = ∫ p, inner ℝ (d p) (d p)
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) :=
      MeasureTheory.L2.inner_def d d
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
              H beta hbeta degree p.1 p.2 -
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
      apply integral_congr_ae
      filter_upwards [(hp.sub ha).coeFn_toLp] with p hpnt
      have hdpoint :
          d p = partialRaw p - actualRaw p := hpnt
      rw [hdpoint]
      exact real_inner_self_eq_norm_sq _

/-- The integrated square distance from the finite four-edge Wilson/Fock
kernel to the actual completed-positive kernel tends to zero.  This is the
cancellation-free dominated-convergence step at the product-kernel level. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_difference_norm_sq_integral_tendsto_zero
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun degree =>
        ∫ p,
          ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
                H beta hbeta degree p.1 p.2 -
              periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
                beta hbeta p.1 p.2‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2))
      atTop (𝓝 0) := by
  let Cpartial :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
      H beta hbeta
  let Csystem := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta
  let Cactual : ℝ := Real.sqrt (Csystem.base.partitionFunction⁻¹)
  let C : ℝ := Cpartial + Cactual
  let F := fun degree
      (p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) =>
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2 -
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
          beta hbeta p.1 p.2‖ ^ 2
  have hF_meas :
      ∀ᶠ degree in atTop,
        AEStronglyMeasurable (F degree)
          (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) :=
    Filter.Eventually.of_forall fun degree => by
      dsimp [F]
      exact
        ((periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_jointMeasurable
            hH beta hbeta degree).sub
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
            H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)).norm.pow_const 2 |>.aestronglyMeasurable
  have hF_bound :
      ∀ᶠ degree in atTop,
        ∀ᵐ p ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2),
          ‖F degree p‖ ≤ C ^ 2 :=
    Filter.Eventually.of_forall fun degree =>
      Filter.Eventually.of_forall fun p => by
        dsimp [F]
        let a := periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2
        let b := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
          beta hbeta p.1 p.2
        have ha : ‖a‖ ≤ Cpartial := by
          dsimp [a, Cpartial]
          simpa [Real.norm_eq_abs] using
            periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
              H beta hbeta degree p.1 p.2
        have hb0 : 0 ≤ b := by
          dsimp [b]
          exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
            H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
            beta hbeta p.1 p.2
        have hbraw : b ≤ Cactual := by
          dsimp [b, Cactual, Csystem]
          exact
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2
        have hb : ‖b‖ ≤ Cactual := by
          rw [Real.norm_eq_abs, abs_of_nonneg hb0]
          exact hbraw
        have hdiff : ‖a - b‖ ≤ C := by
          calc
            ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
            _ ≤ Cpartial + Cactual := add_le_add ha hb
            _ = C := rfl
        change ‖‖a - b‖ ^ 2‖ ≤ C ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a - b‖)]
        exact pow_le_pow_left₀ (norm_nonneg (a - b)) hdiff 2
  have hC_integrable :
      Integrable
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 => C ^ 2)
        (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
    simpa using
      (integrable_const (μ := periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2)
        (C ^ 2))
  have hF_lim :
      ∀ᵐ p ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2),
        Tendsto (fun degree => F degree p) atTop (𝓝 0) :=
    Filter.Eventually.of_forall fun p => by
      dsimp [F]
      have hraw : Tendsto
          (fun degree =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
              H beta hbeta degree p.1 p.2)
          atTop
          (𝓝
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2)) := by
        simpa using
          periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_tendsto
            hH beta hbeta p.1 p.2
      have hconst : Tendsto
          (fun _ : ℕ =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2)
          atTop
          (𝓝
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
              beta hbeta p.1 p.2)) :=
        tendsto_const_nhds
      have hdiff : Tendsto
          (fun degree =>
            periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
                H beta hbeta degree p.1 p.2 -
              periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive
                beta hbeta p.1 p.2)
          atTop (𝓝 0) := by
        simpa using hraw.sub hconst
      simpa using hdiff.norm.pow 2
  have hdom :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (F := F)
      (f := fun _ => (0 : ℝ))
      (fun _ => C ^ 2)
      hF_meas hF_bound hC_integrable hF_lim
  simpa [F] using hdom

/-- The complete finite four-edge Wilson/Fock product kernels converge to the
actual completed-positive Wilson kernel in product-Haar `L²` norm. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2_tendsto_actual
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
          H hH beta hbeta degree)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)) := by
  have hsq :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_difference_norm_sq_integral_tendsto_zero
      hH beta hbeta
  have hsq' : Tendsto
      (fun degree =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
              H hH beta hbeta degree -
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [
      periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2_sub_actual_norm_sq]
      using hsq
  have hsqrt : Tendsto
      (fun degree =>
        Real.sqrt
          (‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
                H hH beta hbeta degree -
              periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
                H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta‖ ^ 2))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq'
  have hnorm : Tendsto
      (fun degree =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
              H hH beta hbeta degree -
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
              H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta‖)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg, norm_nonneg] using hsqrt
  exact (tendsto_iff_norm_sub_tendsto_zero).2 hnorm

/-- Product-`L²` finite kernels rewritten on the literal product measure used
by the generic rectangular Hilbert--Schmidt operator. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    Lp ℝ 2
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  simpa [periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2
      H hH beta hbeta degree)

/-- The finite rectangular kernels converge in the exact product-`L²` carrier
used by the physical Wilson analysis operator. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2_tendsto_actual
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
          H hH beta hbeta degree)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)) := by
  simpa [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialProductL2_tendsto_actual
      hH beta hbeta

/-- Finite Wilson/Fock rectangular analysis operator associated with the full
residual-times-four-edge partial kernel. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
    (H : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H 2) :=
  realL2HilbertSchmidtRectangularKernelOperator
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2
      H hH beta hbeta degree)

/-- Product-`L²` kernel convergence lifts automatically to operator-norm
convergence of the complete finite Wilson/Fock analysis operators. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator_tendsto_actual
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator
          H hH beta hbeta degree)
      atTop
      (𝓝
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)) := by
  have hK :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialRectangularL2_tendsto_actual
      hH beta hbeta
  have hT :=
    realL2HilbertSchmidtRectangularKernelOperator_continuous
      (μ := periodicHypercubicEvenBoundaryHaarMeasure H 2)
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H 2)
  have h := hT.tendsto
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      H 2 cyclicFourEdgeWilsonProductL2LimitTwoRankPositive beta hbeta)
  simpa [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialAnalysisOperator,
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator] using
    h.comp hK

end

end MathlibAnalytic
end MGAP4D