import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWord
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance concreteFiniteTransferWordHaarPathSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance concreteFiniteTransferWordHaarPathSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance concreteFiniteTransferWordHaarPathSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupIsTopologicalGroup N
local instance concreteFiniteTransferWordHaarPathSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupCompactSpace N
local instance concreteFiniteTransferWordHaarPathSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupSecondCountableTopology N
local instance concreteFiniteTransferWordHaarPathSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupMeasurableSpace N
local instance concreteFiniteTransferWordHaarPathSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) := specialUnitaryGroupBorelSpace N

/-- Recursion-friendly count of path slabs consumed by a transfer word.
The successor is placed on the right in consuming-letter cases so deleting
the first path coordinate is definitionally typed. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount
    {H N : ℕ} : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N → ℕ
  | [] => 0
  | letter :: tail =>
      match letter with
      | .transfer =>
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail + 1
      | .slice _ _ =>
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
      | .slab _ _ =>
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail + 1

/-- The recursion-friendly path count agrees with the public slab count. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount_eq_slabCount
    {H N : ℕ}
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount word := by
  induction word with
  | nil => rfl
  | cons letter tail ih =>
      cases letter <;>
        simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount,
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount,
          periodicHypercubicEvenSpecialUnitaryFiniteTransferLetterSlabCount, ih] <;>
        omega

/-- Uniform absolute bound for the literal path weight of a finite word. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound
    {H N : ℕ} : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N → ℝ
  | [] => 1
  | letter :: tail =>
      match letter with
      | .transfer =>
          periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound tail
      | .slice a _ =>
          ‖a‖ * periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound tail
      | .slab b _ =>
          ‖b‖ * periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound tail

theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound_nonneg
    {H N : ℕ}
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound word := by
  induction word with
  | nil => norm_num [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound]
  | cons letter tail ih =>
      cases letter <;>
        simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound, ih,
          mul_nonneg (norm_nonneg _) ih]

/-- Literal chronological path weight of a finite transfer word.

A slice letter multiplies at the current slice and does not advance time.
An ordinary transfer contributes one Wilson slab kernel and advances once.
A slab letter contributes the kernel times its adjacent-slice observable and
advances once. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
    (H N : ℕ)
    (beta : ℝ) :
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) →
    PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word) → ℝ
  | [], _ => 1
  | letter :: tail, path =>
      match letter with
      | .slice a _ =>
          a (path 0) *
            periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta tail path
      | .transfer =>
          let tailPath : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) :=
            fun i => path i.succ
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta (path 0) (tailPath 0) *
            periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta tail tailPath
      | .slab b _ =>
          let tailPath : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) :=
            fun i => path i.succ
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta (path 0) (tailPath 0) *
            b (path 0, tailPath 0) *
            periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta tail tailPath

/-- The literal word path weight is measurable on its finite path space. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight_measurable
    (H N : ℕ)
    (beta : ℝ)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
        H N beta word) := by
  induction word with
  | nil =>
      simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight]
  | cons letter tail ih =>
      cases letter with
      | slice a ha =>
          have ha0 : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
                  (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) =>
                a (path 0)) :=
            a.continuous.measurable.comp (measurable_pi_apply 0)
          have hExplicit : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
                  (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) =>
                a (path 0) *
                  periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                    H N beta tail path) :=
            ha0.mul ih
          have hEq :
              periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                  H N beta (.slice a ha :: tail) =
                fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
                    (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) =>
                  a (path 0) *
                    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                      H N beta tail path := by
            funext path
            rfl
          rw [hEq]
          exact hExplicit
      | transfer =>
          let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
          let tailMap : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) →
              PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n :=
            fun path i => path i.succ
          have htailMap : Measurable tailMap := by
            refine measurable_pi_lambda _ ?_
            intro i
            exact measurable_pi_apply i.succ
          have hpair : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                (path 0, path (0 : Fin (n + 1)).succ)) :=
            (measurable_pi_apply 0).prodMk
              (measurable_pi_apply (0 : Fin (n + 1)).succ)
          have hKernelPair : Measurable
              (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta p.1 p.2) :=
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
              H N beta).measurable
          have hK : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                  H N beta (path 0) (path (0 : Fin (n + 1)).succ)) :=
            hKernelPair.comp hpair
          have hExplicit : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta (path 0) (path (0 : Fin (n + 1)).succ) *
                  periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                    H N beta tail (tailMap path)) :=
            hK.mul (ih.comp htailMap)
          have hEq :
              periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                  H N beta (.transfer :: tail) =
                fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                      H N beta (path 0) (path (0 : Fin (n + 1)).succ) *
                    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                      H N beta tail (tailMap path) := by
            funext path
            rfl
          rw [hEq]
          exact hExplicit
      | slab b hb =>
          let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
          let tailMap : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) →
              PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n :=
            fun path i => path i.succ
          have htailMap : Measurable tailMap := by
            refine measurable_pi_lambda _ ?_
            intro i
            exact measurable_pi_apply i.succ
          have hpair : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                (path 0, path (0 : Fin (n + 1)).succ)) :=
            (measurable_pi_apply 0).prodMk
              (measurable_pi_apply (0 : Fin (n + 1)).succ)
          have hFactorPair : Measurable
              (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta p.1 p.2 * b p) :=
            ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
              H N beta).mul b.continuous).measurable
          have hFactor : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta (path 0) (path (0 : Fin (n + 1)).succ) *
                  b (path 0, path (0 : Fin (n + 1)).succ)) :=
            hFactorPair.comp hpair
          have hExplicit : Measurable
              (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                    H N beta (path 0) (path (0 : Fin (n + 1)).succ) *
                  b (path 0, path (0 : Fin (n + 1)).succ)) *
                    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                      H N beta tail (tailMap path)) :=
            hFactor.mul (ih.comp htailMap)
          have hEq :
              periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                  H N beta (.slab b hb :: tail) =
                fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1) =>
                  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                      H N beta (path 0) (path (0 : Fin (n + 1)).succ) *
                    b (path 0, path (0 : Fin (n + 1)).succ)) *
                      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                        H N beta tail (tailMap path) := by
            funext path
            rfl
          rw [hEq]
          exact hExplicit

/-- The literal word path weight is bounded by the product of observable norms. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word)) :
    |periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta word path| ≤
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound word := by
  induction word with
  | nil =>
      simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight,
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound]
  | cons letter tail ih =>
      cases letter with
      | slice a ha =>
          have ha0 : |a (path 0)| ≤ ‖a‖ := by
            simpa [Real.norm_eq_abs] using a.norm_coe_le_norm (path 0)
          rw [show periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta (.slice a ha :: tail) path =
            a (path 0) * periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta tail path by rfl]
          rw [abs_mul]
          exact mul_le_mul ha0 (ih path) (abs_nonneg _) (norm_nonneg a)
      | transfer =>
          let tailPath : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) :=
            fun i => path i.succ
          have hk :=
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
              H N hN beta hbeta (path 0) (tailPath 0)
          rw [show periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta (.transfer :: tail) path =
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta (path 0) (tailPath 0) *
              periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                H N beta tail tailPath by rfl]
          rw [abs_mul]
          calc
            _ ≤ 1 * periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound tail := by
              exact mul_le_mul hk (ih tailPath) (abs_nonneg _) zero_le_one
            _ = periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound
                (.transfer :: tail) := by
              simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound]
      | slab b hb =>
          let tailPath : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
              (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail) :=
            fun i => path i.succ
          have hk :=
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
              H N hN beta hbeta (path 0) (tailPath 0)
          have hb0 : |b (path 0, tailPath 0)| ≤ ‖b‖ := by
            simpa [Real.norm_eq_abs] using b.norm_coe_le_norm (path 0, tailPath 0)
          rw [show periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
              H N beta (.slab b hb :: tail) path =
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta (path 0) (tailPath 0) * b (path 0, tailPath 0) *
              periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight
                H N beta tail tailPath by rfl]
          rw [abs_mul, abs_mul]
          calc
            _ ≤ 1 * ‖b‖ * periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound tail := by
              exact mul_le_mul
                (mul_le_mul hk hb0 (abs_nonneg _) zero_le_one)
                (ih tailPath) (abs_nonneg _) (mul_nonneg zero_le_one (norm_nonneg b))
            _ = periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound
                (.slab b hb :: tail) := by
              simp [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound]

/-- One literal finite product-Haar path integral attached to an arbitrary
chronological transfer word. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
    (H N : ℕ)
    (beta : ℝ)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) : ℝ :=
  ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word),
    f (path 0) *
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta word path *
      g (path (Fin.last
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word)))
    ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word))

private theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordWeightedRight_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word) =>
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta word path *
          g (path (Fin.last
            (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word))))
      (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word
  let pathμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let B := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound word
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeightBound_nonneg word
  have hg1 : Integrable (fun A => g A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp g).mono_exponent (by norm_num)
  have hglast : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        g (path (Fin.last n))) pathμ := by
    simpa [pathμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure, μ] using
      (MeasureTheory.integrable_comp_eval
        (μ := fun _ : Fin (n + 1) => μ) (i := Fin.last n) hg1)
  have hmajor : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        B * ‖g (path (Fin.last n))‖) pathμ := by
    simpa [Pi.smul_apply, smul_eq_mul] using hglast.norm.smul B
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta word path *
          g (path (Fin.last n))) pathμ :=
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight_measurable
      H N beta word).aestronglyMeasurable.mul hglast.aestronglyMeasurable
  apply hmajor.mono hmeas
  filter_upwards with path
  have hw := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight_abs_le
    H N hN beta hbeta word path
  change
    ‖periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta word path *
        g (path (Fin.last n))‖ ≤
      ‖B * ‖g (path (Fin.last n))‖‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hB, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)

private theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferFirstStepHaarIntegral_eq
    (H N : ℕ)
    (n : ℕ)
    (q : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hqmeas : Measurable q)
    (hqbound : ∀ p, |q p| ≤ C)
    (w : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n → ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
    (hRight : Integrable
      (fun tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        w tail * g (tail (Fin.last n)))
      (periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n))
    (Qf : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
    (hQf : Qf =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun B => ∫ A, f A * q (A, B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1),
      f (path 0) *
        q (path 0, path (0 : Fin (n + 1)).succ) *
        w (fun i : Fin (n + 1) => path i.succ) *
        g (path (Fin.last (n + 1)))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N (n + 1))) =
      ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        Qf (tail 0) * w tail * g (tail (Fin.last n))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let tailμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  let F := fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
    (f p.1 * (w p.2 * g (p.2 (Fin.last n)))) * q (p.1, p.2 0)
  have hf1 : Integrable (fun A => f A) μ := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp f).mono_exponent (by norm_num)
  have hbase : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        f p.1 * (w p.2 * g (p.2 (Fin.last n)))) (μ.prod tailμ) :=
    hf1.mul_prod hRight
  have hq : Measurable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        q (p.1, p.2 0)) :=
    hqmeas.comp
      (measurable_fst.prodMk
        ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd))
  have hmajor : Integrable
      (fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        C * (f p.1 * (w p.2 * g (p.2 (Fin.last n))))) (μ.prod tailμ) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.smul C
  have hF : Integrable F (μ.prod tailμ) := by
    apply hmajor.mono (hbase.aestronglyMeasurable.mul hq.aestronglyMeasurable)
    filter_upwards with p
    let base := f p.1 * (w p.2 * g (p.2 (Fin.last n)))
    change |base * q (p.1, p.2 0)| ≤ |C * base|
    have hmul := mul_le_mul_of_nonneg_left
      (hqbound (p.1, p.2 0)) (abs_nonneg base)
    simpa [base, abs_mul, abs_of_nonneg hC, mul_comm, mul_left_comm, mul_assoc] using hmul
  let μs : Fin (n + 2) → Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := fun _ => μ
  have hMP := MeasureTheory.measurePreserving_piFinSuccAbove μs (0 : Fin (n + 2))
  calc
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N (n + 1),
      f (path 0) * q (path 0, path (0 : Fin (n + 1)).succ) *
        w (fun i : Fin (n + 1) => path i.succ) * g (path (Fin.last (n + 1)))
      ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N (n + 1))) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        F p ∂(μ.prod tailμ) := by
      unfold periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
      change (∫ path : Fin (n + 2) →
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f (path 0) * q (path 0, path (0 : Fin (n + 1)).succ) *
          w (fun i : Fin (n + 1) => path i.succ) * g (path (Fin.last (n + 1)))
        ∂(Measure.pi μs)) = _
      rw [← hMP.symm.integral_comp']
      apply integral_congr_ae
      filter_upwards with p
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
      simp [F, Fin.cons_zero, Fin.cons_succ]
      ring
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        (∫ A, f A * q (A, tail 0) ∂μ) * w tail * g (tail (Fin.last n)) ∂tailμ := by
      rw [MeasureTheory.integral_prod_symm _ hF]
      apply integral_congr_ae
      filter_upwards with tail
      calc
        (∫ A, F (A, tail) ∂μ) =
          ∫ A, (f A * q (A, tail 0)) *
            (w tail * g (tail (Fin.last n))) ∂μ := by
              apply integral_congr_ae
              filter_upwards with A
              simp [F]
              ring
        _ = (∫ A, f A * q (A, tail 0) ∂μ) *
            (w tail * g (tail (Fin.last n))) := by
              rw [integral_mul_const]
        _ = (∫ A, f A * q (A, tail 0) ∂μ) * w tail *
            g (tail (Fin.last n)) := by ring
    _ = ∫ tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n,
        Qf (tail 0) * w tail * g (tail (Fin.last n)) ∂tailμ := by
      have hQfTail :
          (fun tail : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
            Qf (tail 0)) =ᵐ[tailμ]
          (fun tail => ∫ A, f A * q (A, tail 0) ∂μ) := by
        simpa [tailμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure, μ] using
          ((MeasureTheory.measurePreserving_eval
            (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hQf)
      apply integral_congr_ae
      filter_upwards [hQfTail] with tail htail
      rw [htail]

/-- A slice letter is absorbed by the literal Haar path integral as pointwise multiplication. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_slice
    (H N : ℕ)
    (beta : ℝ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (tail : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
        H N beta (.slice a ha :: tail) f g =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta tail
        (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a f) g := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
  let pathμ := periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure H N n
  have hMa :
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a f =ᵐ[μ]
        fun A => a A * f A := by
    simpa using
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn H N a f
  have hMaPath :
      (fun path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath H N n =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulOperator H N a f
          (path 0)) =ᵐ[pathμ]
      (fun path => a (path 0) * f (path 0)) := by
    simpa [pathμ, periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure, μ] using
      ((MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1))).quasiMeasurePreserving.ae_eq hMa)
  unfold periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
  apply integral_congr_ae
  filter_upwards [hMaPath] with path hpath
  simp only [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight]
  rw [hpath]
  ring_nf

/-- An ordinary transfer letter is absorbed as the actual one-slab transfer operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_transfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (tail : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
        H N beta (.transfer :: tail) f g =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta tail
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f) g := by
  let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
  let q := fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2
  let w := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta tail
  have hRight := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordWeightedRight_integrable
    H N hN beta hbeta tail g
  have hqmeas : Measurable q :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta).measurable
  have hqbound : ∀ p, |q p| ≤ (1 : ℝ) := fun p =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 p.2
  have hQf := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_coeFn
    H N hN beta hbeta f
  have hQf' :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN beta hbeta f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
        fun B => ∫ A, f A * q (A, B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
    simpa [q, periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferIntegralRepresentative]
      using hQf
  have hflat := periodicHypercubicEvenSpecialUnitaryFiniteTransferFirstStepHaarIntegral_eq
    H N n q 1 zero_le_one hqmeas hqbound w f g hRight
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta f) hQf'
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight, n, q, w, mul_assoc] using hflat

/-- A slab-observable letter is absorbed as the one-slab pair-insertion operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_slab
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (tail : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
        H N beta (.slab b hb :: tail) f g =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta tail
        (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f) g := by
  let n := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount tail
  let q := fun p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 * b p
  let w := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight H N beta tail
  have hRight := periodicHypercubicEvenSpecialUnitaryFiniteTransferWordWeightedRight_integrable
    H N hN beta hbeta tail g
  have hqmeas : Measurable q :=
    ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H N beta).mul
      b.continuous).measurable
  have hqbound : ∀ p, |q p| ≤ ‖b‖ := by
    intro p
    rw [abs_mul]
    have hk := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H N hN beta hbeta p.1 p.2
    have hbnd : |b p| ≤ ‖b‖ := by
      simpa [Real.norm_eq_abs] using b.norm_coe_le_norm p
    calc
      _ ≤ 1 * ‖b‖ := mul_le_mul hk hbnd (abs_nonneg _) zero_le_one
      _ = ‖b‖ := by simp
  have hQf := periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator_coeFn
    H N hN beta hbeta b f
  have hQf' :
      periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
          H N hN beta hbeta b f =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
        fun B => ∫ A, f A * q (A, B)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
    filter_upwards [hQf] with B hB
    rw [hB]
    unfold periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableIntegralRepresentative
    apply integral_congr_ae
    filter_upwards with A
    simp [q]
    ring
  have hflat := periodicHypercubicEvenSpecialUnitaryFiniteTransferFirstStepHaarIntegral_eq
    H N n q ‖b‖ (norm_nonneg b) hqmeas hqbound w f g hRight
    (periodicHypercubicEvenSpecialUnitaryOneSlabPairObservableOperator
      H N hN beta hbeta b f) hQf'
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight, n, q, w, mul_assoc] using hflat

/-- The empty word is the zero-slab Haar pairing. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_nil
    (H N : ℕ)
    (beta : ℝ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude
        H N beta [] f g = inner ℝ f g := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathWeight,
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude,
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel] using
    (periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugeEndpointAmplitude_zero
      H N beta f g)

/-- Arbitrary finite chronological words have exactly the same matrix
coefficients whether read as one literal product-Haar path integral or as the
concrete ambient transfer-word operator. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_eq_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta word f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta word f) g := by
  induction word generalizing f with
  | nil =>
      simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator] using
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_nil H N beta f g)
  | cons letter tail ih =>
      cases letter with
      | slice a ha =>
          rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_slice]
          rw [ih]
          rfl
      | transfer =>
          rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_transfer
            H N hN beta hbeta]
          rw [ih]
          rfl
      | slab b hb =>
          rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_slab
            H N hN beta hbeta]
          rw [ih]
          rfl

/-- The same exact Haar path formula on the genuine Gauss-law physical Hilbert sector. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta word f) g =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta word
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  change inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta word f :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) = _
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_coe]
  symm
  exact periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_eq_inner
    H N hN beta hbeta word
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)

/-- The arbitrary-word literal semantics specializes to the earlier single-slice insertion. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_haarAmplitude_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N)
    (ha : periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant H N a)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryTransferSliceObservableAmplitude H N beta left right a
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [← periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord_inner_eq_amplitude
    H N hN beta hbeta left right a ha f g]
  symm
  exact periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
    H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSliceInsertionWord H N left right a ha) f g

/-- The arbitrary-word literal semantics specializes to the earlier single-slab pair insertion. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_haarAmplitude_eq_amplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N)
    (hb : periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N b)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude H N beta left right b
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) := by
  rw [← periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_inner_eq_amplitude
    H N hN beta hbeta left right b hb f g]
  symm
  exact periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
    H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord H N left right b hb) f g

structure PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordHaarPathPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  slabCountAgreement : ∀ word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N,
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount word =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount word
  ambientExact : ∀ (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
      (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N),
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta word f g =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordAmbientOperator
          H N hN beta hbeta word f) g
  physicalExact : ∀ (word : PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N)
      (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N),
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta word f) g =
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta word
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)

theorem periodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordHaarPathPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWordHaarPathPackage
      H N hN beta hbeta :=
  { slabCountAgreement :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPathSlabCount_eq_slabCount
    ambientExact :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude_eq_inner
        H N hN beta hbeta
    physicalExact :=
      periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D
