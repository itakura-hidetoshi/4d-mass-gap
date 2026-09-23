import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroRankOne
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNonnegativeTopEigenvector
import Mathlib.Tactic

/-!
# Canonical beta-zero nonnegative physical vacuum

At beta = 0 the genuine physical one-slab transfer is the rank-one projection
onto the canonical constant Gauss-law unit vector.

The previously chosen abstract top eigenvector may differ from that reference
vector by a real unit scalar.  Taking the canonical pointwise absolute value
removes that irrelevant sign.  Therefore the repository's canonical
nonnegative top eigenvector is exactly the constant physical unit vector at
beta = 0.

This is the canonicalization needed before reducing the beta-zero vacuum and
ground-state joint measures to Haar and pair Haar.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- Pointwise absolute value on real L2 intertwines real scalar multiplication
with the absolute value of the scalar. -/
theorem realL2Abs_smul
    {α : Type u}
    [MeasurableSpace α]
    {μ : Measure α}
    (c : ℝ)
    (f : Lp ℝ 2 μ) :
    realL2Abs (c • f) = |c| • realL2Abs f := by
  apply Lp.ext
  filter_upwards [
    realL2Abs_coeFn (c • f),
    Lp.coeFn_smul c f,
    realL2Abs_coeFn f,
    Lp.coeFn_smul |c| (realL2Abs f)] with x hAbs hSmul hF hOut
  rw [hAbs, hOut, hSmul, hF]
  exact abs_mul c (f x)

/-- The physical absolute-value operation obeys the same scalar rule. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_smul
    (H N : ℕ)
    (c : ℝ)
    (f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N (c • f) =
      |c| •
        periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N f := by
  apply Subtype.ext
  change
    realL2Abs
        (c •
          (f :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      |c| •
        realL2Abs
          (f :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact
    realL2Abs_smul c
      (f :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))

/-- The canonical physical constant unit vector is fixed by pointwise absolute
value. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_constantUnit
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N := by
  apply Subtype.ext
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneL2 : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  change realL2Abs oneL2 = oneL2
  apply Lp.ext
  have hOne :
      oneL2 =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa [oneL2] using
      (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ)))
  filter_upwards [realL2Abs_coeFn oneL2, hOne] with x hAbs hOneX
  rw [hAbs, hOneX]
  norm_num

/-- At beta = 0 the chosen abstract physical top eigenvector lies on the
canonical constant line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_zero_eq_inner_smul_constantUnit
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN 0 (by norm_num) =
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
            H N hN 0 (by norm_num)) •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN 0 (by norm_num)
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN 0 (by norm_num)
  let u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hEig :
      T Ω = Ω := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
        H N hN 0 (by norm_num)
    change T Ω = ‖T‖ • Ω at h
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
        H N hN,
      one_smul] at h
    exact h
  have hRank :
      T Ω = inner ℝ u Ω • u := by
    simpa [T, Ω, u] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_apply
        H N hN Ω)
  change Ω = inner ℝ u Ω • u
  exact hEig.symm.trans hRank

/-- The scalar relating the chosen beta-zero top eigenvector to the canonical
constant unit vector has absolute value one. -/
theorem
    abs_inner_physicalConstantUnit_topEigenvector_zero
    (H N : ℕ)
    (hN : 0 < N) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN 0 (by norm_num))| = 1 := by
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN 0 (by norm_num)
  let u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let c : ℝ := inner ℝ u Ω
  have hLine : Ω = c • u := by
    simpa [Ω, u, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_zero_eq_inner_smul_constantUnit
        H N hN)
  have hΩNorm : ‖Ω‖ = 1 := by
    simpa [Ω] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
        H N hN 0 (by norm_num))
  have huNorm : ‖u‖ = 1 := by
    simpa [u] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N)
  have hNorm := congrArg norm hLine
  rw [hΩNorm, norm_smul, Real.norm_eq_abs, huNorm, mul_one] at hNorm
  change |c| = 1
  exact hNorm.symm

/-- Canonical endpoint identification: the repository's nonnegative physical
top eigenvector is exactly the constant Gauss-law unit vector at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N := by
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN 0 (by norm_num)
  let u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let c : ℝ := inner ℝ u Ω
  have hLine : Ω = c • u := by
    simpa [Ω, u, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_zero_eq_inner_smul_constantUnit
        H N hN)
  have hAbs : |c| = 1 := by
    simpa [Ω, u, c] using
      (abs_inner_physicalConstantUnit_topEigenvector_zero H N hN)
  change periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs H N Ω = u
  rw [
    hLine,
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_smul,
    hAbs,
    one_smul,
    periodicHypercubicEvenSpecialUnitaryPhysicalRealL2Abs_constantUnit]

end

end MGAP4D.MathlibAnalytic
