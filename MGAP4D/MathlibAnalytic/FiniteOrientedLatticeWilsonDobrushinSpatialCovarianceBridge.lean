import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinPathGreenTail
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanTemporalCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Static Gibbs covariance of two real observables. -/
def FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) : ℝ :=
  L.gibbsPairingReal
    (fun A => f A - L.gibbsExpectationReal f)
    (fun A => g A - L.gibbsExpectationReal g)

/-- Two physical-link supports are separated by at least `d` active
plaquette-neighbor steps when no link of the right support belongs to an
`m`-step ball from the left support for any `m < d`. -/
def FiniteOrientedLatticeWilsonSystem.activePlaquetteNeighborSeparatedAtLeast
    (L : FiniteOrientedLatticeWilsonSystem)
    (left right : Finset L.Edge)
    (d : ℕ) : Prop :=
  ∀ target : L.Edge,
    target ∈ left →
      ∀ source : L.Edge,
        source ∈ right →
          ∀ m : ℕ,
            m < d →
              source ∉ L.activePlaquetteNeighborBall {target} m

/-- Active-neighbor separation eliminates every influence path shorter than the
separation scale. -/
theorem finite_oriented_influencePathKernel_eq_zero_of_separated
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (left right : Finset L.Edge)
    (d : ℕ)
    (hSeparated :
      L.activePlaquetteNeighborSeparatedAtLeast left right d)
    (target source : L.Edge)
    (hTarget : target ∈ left)
    (hSource : source ∈ right)
    (m : ℕ)
    (hm : m < d) :
    D.influencePathKernel m target source = 0 :=
  finite_oriented_influencePathKernel_eq_zero_of_not_mem_activeBall
    D S m target source
      (hSeparated target hTarget source hSource m hm)

/-- A Green kernel between separated supports has no contribution from path
lengths below `d`, so its full series equals its tail starting at `d`. -/
theorem finite_oriented_influenceGreenTail_zero_eq_tail_of_separated
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (left right : Finset L.Edge)
    (d : ℕ)
    (hSeparated :
      L.activePlaquetteNeighborSeparatedAtLeast left right d)
    (target source : L.Edge)
    (hTarget : target ∈ left)
    (hSource : source ∈ right) :
    D.influenceGreenTail 0 target source =
      D.influenceGreenTail d target source := by
  classical
  let path : ℕ → ℝ := fun m =>
    D.influencePathKernel m target source
  have hSummable : Summable path := by
    simpa [path,
      FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail] using
      (finite_oriented_influenceGreenTail_summable
        D 0 target source)
  have hPrefix :
      (∑ m ∈ Finset.range d, path m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    exact finite_oriented_influencePathKernel_eq_zero_of_separated
      D S left right d hSeparated target source
        hTarget hSource m (Finset.mem_range.mp hm)
  have hSplit := hSummable.sum_add_tsum_nat_add d
  rw [hPrefix, zero_add] at hSplit
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail
  change
    (∑' r : ℕ, path (0 + r)) =
      ∑' r : ℕ, path (d + r)
  simpa [Nat.add_comm] using hSplit.symm

/-- Every pointwise Green tail is nonnegative. -/
theorem finite_oriented_influenceGreenTail_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (d : ℕ)
    (target source : L.Edge) :
    0 ≤ D.influenceGreenTail d target source := by
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail
  exact tsum_nonneg fun r =>
    finite_oriented_influencePathKernel_nonneg
      D (d + r) target source

/-- Proof-relevant boundary between the established Green-kernel estimates and
the still-independent Dobrushin covariance comparison theorem.

A future theorem may construct this certificate from the one-link conditional
expectation comparison.  This file does not assume that construction silently. -/
structure FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) : Prop where
  covariance_abs_le :
    ∀ {f g : L.Configuration → ℝ},
      ∀ (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f),
        ∀ (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g),
          |L.gibbsCovarianceReal f g| ≤
            ∑ target : L.Edge,
              ∑ source : L.Edge,
                P.variation target *
                  D.influenceGreenTail 0 target source *
                    Q.variation source

/-- Under a Green-kernel covariance comparison certificate, observables whose
variation profiles are supported on active-neighbor-separated sets have static
Gibbs covariance bounded by the geometric Green tail. -/
theorem
    FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison.gibbsCovarianceReal_abs_le_of_separated
    {L : FiniteOrientedLatticeWilsonSystem}
    {D : FiniteOrientedLatticeWilsonDobrushinMatrixData L}
    (C : FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison D)
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (left right : Finset L.Edge)
    (hPSupport :
      ∀ target : L.Edge,
        target ∉ left → P.variation target = 0)
    (hQSupport :
      ∀ source : L.Edge,
        source ∉ right → Q.variation source = 0)
    (d : ℕ)
    (hSeparated :
      L.activePlaquetteNeighborSeparatedAtLeast left right d) :
    |L.gibbsCovarianceReal f g| ≤
      (∑ target : L.Edge, P.variation target) *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) *
            ∑ source : L.Edge, Q.variation source := by
  classical
  have hTailNonneg :
      0 ≤ D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient) :=
    div_nonneg
      (pow_nonneg D.dobrushinCoefficient_nonneg d)
      (sub_nonneg.mpr (le_of_lt D.dobrushinCoefficient_lt_one))
  calc
    |L.gibbsCovarianceReal f g| ≤
        ∑ target : L.Edge,
          ∑ source : L.Edge,
            P.variation target *
              D.influenceGreenTail 0 target source *
                Q.variation source :=
      C.covariance_abs_le P Q
    _ ≤ ∑ target : L.Edge,
        ∑ source : L.Edge,
          P.variation target *
            (D.dobrushinCoefficient ^ d /
              (1 - D.dobrushinCoefficient)) *
                Q.variation source := by
      apply Finset.sum_le_sum
      intro target _hTargetUniv
      apply Finset.sum_le_sum
      intro source _hSourceUniv
      by_cases hTarget : target ∈ left
      · by_cases hSource : source ∈ right
        · have hGreenEq :=
            finite_oriented_influenceGreenTail_zero_eq_tail_of_separated
              D S left right d hSeparated
                target source hTarget hSource
          have hGreenLe :
              D.influenceGreenTail 0 target source ≤
                D.dobrushinCoefficient ^ d /
                  (1 - D.dobrushinCoefficient) := by
            rw [hGreenEq]
            exact finite_oriented_influenceGreenTail_le
              D d target source
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              hGreenLe (P.variation_nonneg target))
            (Q.variation_nonneg source)
        · rw [hQSupport source hSource]
          simp
      · rw [hPSupport target hTarget]
        simp
    _ = (∑ target : L.Edge, P.variation target) *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) *
            ∑ source : L.Edge, Q.variation source := by
      calc
        (∑ target : L.Edge,
          ∑ source : L.Edge,
            P.variation target *
              (D.dobrushinCoefficient ^ d /
                (1 - D.dobrushinCoefficient)) *
                  Q.variation source) =
            ∑ target : L.Edge,
              (P.variation target *
                (D.dobrushinCoefficient ^ d /
                  (1 - D.dobrushinCoefficient))) *
                    ∑ source : L.Edge, Q.variation source := by
          apply Finset.sum_congr rfl
          intro target _hTarget
          rw [Finset.mul_sum]
        _ = (∑ target : L.Edge,
              P.variation target *
                (D.dobrushinCoefficient ^ d /
                  (1 - D.dobrushinCoefficient))) *
                    ∑ source : L.Edge, Q.variation source := by
          rw [Finset.sum_mul]
        _ = (∑ target : L.Edge, P.variation target) *
              (D.dobrushinCoefficient ^ d /
                (1 - D.dobrushinCoefficient)) *
                    ∑ source : L.Edge, Q.variation source := by
          rw [Finset.sum_mul]

/-- Conditional spatial covariance decay for two selected periodic `Z₂`
plaquettes.  The only remaining independent input is the explicit
Green-kernel covariance comparison certificate. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_greenTail
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (S : FiniteOrientedLatticeWilsonDobrushinActiveSupport D)
    (C : FiniteOrientedLatticeWilsonDobrushinGreenCovarianceComparison D)
    (d : ℕ)
    (hSeparated :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.activePlaquetteNeighborSeparatedAtLeast
          (periodicHypercubicPlaquetteEdges n sourcePlaquette)
          (periodicHypercubicPlaquetteEdges n targetPlaquette) d) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) := by
  have hGeneral :=
    C.gibbsCovarianceReal_abs_le_of_separated S
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta sourcePlaquette)
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta targetPlaquette)
      (periodicHypercubicPlaquetteEdges n sourcePlaquette)
      (periodicHypercubicPlaquetteEdges n targetPlaquette)
      (by
        intro target hOutside
        rw [
          z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_variation,
          periodicHypercubicPlaquetteObservableLinkVariation_eq]
        exact if_neg hOutside)
      (by
        intro source hOutside
        rw [
          z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_variation,
          periodicHypercubicPlaquetteObservableLinkVariation_eq]
        exact if_neg hOutside)
      d hSeparated
  have hSourceSum :=
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_sum_le_four
      n beta hBeta sourcePlaquette
  have hTargetSum :=
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_sum_le_four
      n beta hBeta targetPlaquette
  have hTailNonneg :
      0 ≤ D.dobrushinCoefficient ^ d /
        (1 - D.dobrushinCoefficient) :=
    div_nonneg
      (pow_nonneg D.dobrushinCoefficient_nonneg d)
      (sub_nonneg.mpr (le_of_lt D.dobrushinCoefficient_lt_one))
  have hTargetSumNonneg :
      0 ≤ ∑ source : PeriodicHypercubicEdge n,
        (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
          n beta hBeta targetPlaquette).variation source :=
    Finset.sum_nonneg fun source _hSource =>
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta targetPlaquette).variation_nonneg source
  calc
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      (∑ target : PeriodicHypercubicEdge n,
        (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
          n beta hBeta sourcePlaquette).variation target) *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) *
            ∑ source : PeriodicHypercubicEdge n,
              (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
                n beta hBeta targetPlaquette).variation source := hGeneral
    _ ≤ 4 *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) *
            ∑ source : PeriodicHypercubicEdge n,
              (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
                n beta hBeta targetPlaquette).variation source :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hSourceSum hTailNonneg)
        hTargetSumNonneg
    _ ≤ 4 *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) * 4 :=
      mul_le_mul_of_nonneg_left hTargetSum
        (mul_nonneg (by norm_num) hTailNonneg)
    _ = 16 *
        (D.dobrushinCoefficient ^ d /
          (1 - D.dobrushinCoefficient)) := by
      ring

end

end MathlibAnalytic
end MGAP4D
