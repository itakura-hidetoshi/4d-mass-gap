import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0AllPlaquetteGibbsCovarianceL1V5_PZ37AMJ
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinSchurL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMK — genuine original beta0 SU2 Gibbs plaquette covariance Schur L2

AMJ proves the exact full interacting compact-Haar Wilson Gibbs covariance
absolute L1 row budget 96/(1-rho0), uniform in H. This file upgrades that
finite-volume physical-plaquette kernel to a uniform real ell2 covariance
operator estimate, using the existing certified finite Schur inequality.

The kernel entries are the actual Gibbs covariances of the genuine four-edge
SU2 fundamental plaquette characters. No independent plaquette measure,
surrogate covariance, random-scan-time/Euclidean-time identification,
OS transfer-gap or continuum mass-gap assumption is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- An absolute row-and-column bound for a finite REAL signed kernel gives
a squared ell2 operator norm bound. This statement does not require positivity
of the signed kernel; the comparison matrix is its entrywise absolute value. -/
theorem finiteRealKernel_l2_sq_le_of_abs_row_column
    {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hRows : ∀ i : ι, (∑ j : ι, |K i j|) ≤ c)
    (hCols : ∀ j : ι, (∑ i : ι, |K i j|) ≤ c)
    (a : ι → ℝ) :
    (∑ i : ι, (∑ j : ι, K i j * a j) ^ 2) ≤
      c ^ 2 * ∑ j : ι, a j ^ 2 := by
  classical
  let M : ι → ι → ℝ := fun i j => |K i j|
  let b : ι → ℝ := fun j => |a j|
  have hMNonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact abs_nonneg _
  have hMRows : ∀ i : ι, (∑ j : ι, M i j) ≤ c := by
    intro i
    exact hRows i
  have hMCols : ∀ j : ι, (∑ i : ι, M i j) ≤ c := by
    intro j
    exact hCols j
  have hAbsSum (i : ι) :
      |∑ j : ι, K i j * a j| ≤ ∑ j : ι, M i j * b j := by
    calc
      |∑ j : ι, K i j * a j| ≤
          ∑ j : ι, |K i j * a j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : ι, M i j * b j := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [abs_mul, M, b]
  have hComparisonNonneg (i : ι) :
      0 ≤ ∑ j : ι, M i j * b j := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (hMNonneg i j) (abs_nonneg _)
  have hSqCompare (i : ι) :
      (∑ j : ι, K i j * a j) ^ 2 ≤
        (∑ j : ι, M i j * b j) ^ 2 := by
    have hProd :
        0 ≤ ((∑ j : ι, M i j * b j) - |∑ j : ι, K i j * a j|) *
          ((∑ j : ι, M i j * b j) + |∑ j : ι, K i j * a j|) :=
      mul_nonneg (sub_nonneg.mpr (hAbsSum i))
        (add_nonneg (hComparisonNonneg i) (abs_nonneg _))
    nlinarith [sq_abs (∑ j : ι, K i j * a j)]
  have hRowSq (i : ι) :
      (∑ j : ι, M i j * b j) ^ 2 ≤
        c * ∑ j : ι, M i j * b j ^ 2 :=
    FiniteNonnegativeSchur.row_action_sq_le M hMNonneg c hMRows b i
  have hColumnMass :
      (∑ i : ι, ∑ j : ι, M i j * b j ^ 2) ≤
        c * ∑ j : ι, b j ^ 2 := by
    calc
      (∑ i : ι, ∑ j : ι, M i j * b j ^ 2) =
          ∑ j : ι, (∑ i : ι, M i j) * b j ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ ≤ ∑ j : ι, c * b j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hMCols j) (sq_nonneg _)
      _ = c * ∑ j : ι, b j ^ 2 := by
        rw [Finset.mul_sum]
  calc
    (∑ i : ι, (∑ j : ι, K i j * a j) ^ 2) ≤
        ∑ i : ι, (∑ j : ι, M i j * b j) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => hSqCompare i
    _ ≤ ∑ i : ι, c * ∑ j : ι, M i j * b j ^ 2 := by
      exact Finset.sum_le_sum fun i _ => hRowSq i
    _ = c * ∑ i : ι, ∑ j : ι, M i j * b j ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ c * (c * ∑ j : ι, b j ^ 2) :=
      mul_le_mul_of_nonneg_left hColumnMass hc
    _ = c ^ 2 * ∑ j : ι, a j ^ 2 := by
      simp only [b, sq_abs]
      ring

/-- Actual compact-Haar Wilson Gibbs covariance is symmetric, because the
integral pairing is commutative and the two Gibbs means are real scalars. -/
theorem compactOrientedGibbsCovarianceReal_symm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f g : C.base.Configuration → ℝ) :
    C.gibbsCovarianceReal f g = C.gibbsCovarianceReal g f := by
  have hPair : C.gibbsPairingReal f g = C.gibbsPairingReal g f := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsPairingReal
    apply integral_congr_ae
    filter_upwards [] with A
    exact mul_comm (f A) (g A)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsCovarianceReal
  rw [hPair]
  ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "beta0" => GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling

private instance p4Q2PZ37AMK_nezero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
private instance p4Q2PZ37AMK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
private instance p4Q2PZ37AMK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
private instance p4Q2PZ37AMK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
private instance p4Q2PZ37AMK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
private instance p4Q2PZ37AMK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private instance p4Q2PZ37AMK_nontrivial : Nontrivial G := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : G => (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace GroundStatePosteriorJoint

/-- True original beta0 interacting SU2 Wilson Gibbs covariance is an ell2-
bounded signed operator on the FULL physical plaquette carrier. For all real
plaquette weights a, the squared operator norm is bounded by the squared
AMJ constant, uniformly over all finite H>0. Unlike a random-scan transition,
this matrix is the actual static connected Gibbs covariance kernel.

This does NOT identify the matrix with a physical OS one-slab transfer or
prove an OS transfer spectral gap, spatial exponential decay, or a continuum
Yang--Mills mass gap. -/
theorem p4Q2PZ37AMK_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l2_sq_le
    (H : ℕ) (hH : 0 < H)
    (a : PeriodicHypercubicEvenPlaquette H → ℝ) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      (∑ q : PeriodicHypercubicEvenPlaquette H,
        (p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q A)
          (fun A => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p A) *
            a q) ^ 2) ≤
      (96 * (1 - 18 *
        periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹) ^ 2 *
          ∑ q : PeriodicHypercubicEvenPlaquette H, a q ^ 2 := by
  classical
  let C := p4Q2PZ37AMG_originalFixedBeta0System H
  let chi : PeriodicHypercubicEvenPlaquette H →
      BoundedContinuousFunction C.base.Configuration ℝ :=
    fun q => p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q
  let K : PeriodicHypercubicEvenPlaquette H →
      PeriodicHypercubicEvenPlaquette H → ℝ :=
    fun p q => C.gibbsCovarianceReal (fun A => chi q A) (fun A => chi p A)
  let B : ℝ :=
    96 * (1 - 18 *
      periodicHypercubicSpecialUnitaryActiveTVMajorant beta0)⁻¹
  have hGap :
      0 ≤ 1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta0 := by
    have hStrict := p4Q2PZ37AMG_originalFixedBeta0ActiveTVMajorant_strict
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hGap)
  have hRow (p : PeriodicHypercubicEvenPlaquette H) :
      (∑ q : PeriodicHypercubicEvenPlaquette H, |K p q|) ≤ B := by
    simpa only [K, chi, C, B] using
      p4Q2PZ37AMJ_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l1_le
        H hH p
  have hSymm (p q : PeriodicHypercubicEvenPlaquette H) :
      K p q = K q p := by
    dsimp only [K]
    exact compactOrientedGibbsCovarianceReal_symm C _ _
  have hColumn (q : PeriodicHypercubicEvenPlaquette H) :
      (∑ p : PeriodicHypercubicEvenPlaquette H, |K p q|) ≤ B := by
    calc
      (∑ p : PeriodicHypercubicEvenPlaquette H, |K p q|) =
          ∑ p : PeriodicHypercubicEvenPlaquette H, |K q p| := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hSymm p q]
      _ ≤ B := hRow q
  have hSchur :=
    finiteRealKernel_l2_sq_le_of_abs_row_column K B hB hRow hColumn a
  simpa only [K, chi, C, B] using hSchur

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.finiteRealKernel_l2_sq_le_of_abs_row_column
#print axioms MGAP4D.MathlibAnalytic.compactOrientedGibbsCovarianceReal_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMK_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_l2_sq_le
