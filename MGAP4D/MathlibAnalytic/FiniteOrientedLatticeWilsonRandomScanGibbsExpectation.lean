import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanObservableOscillation
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPairingSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The variation-oriented conditional average introduced for the Dobrushin
chain is definitionally the established one-link heat-bath projection. -/
private theorem randomScanGibbs_singleLinkAverage_eq_projection
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (target : L.Edge) :
    (fun A => L.singleLinkConditionalAverage f A target) =
      L.singleLinkHeatBathProjection target f := by
  funext A
  rfl

/-- Pairing against the constant-one observable is Gibbs expectation. -/
private theorem randomScanGibbs_pairing_one_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal f (fun _ : L.Configuration => (1 : ℝ)) =
      L.gibbsExpectationReal f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Gibbs expectation commutes with multiplication by a real scalar. -/
private theorem randomScanGibbs_expectation_const_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (fun A => c * f A) =
      c * L.gibbsExpectationReal f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  calc
    (∑ A : L.Configuration,
      L.gibbsProbabilityReal A * (c * f A)) =
        ∑ A : L.Configuration,
          c * (L.gibbsProbabilityReal A * f A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ = c * ∑ A : L.Configuration,
        L.gibbsProbabilityReal A * f A := by
      rw [Finset.mul_sum]

/-- Gibbs expectation commutes with a finite sum of real observables. -/
private theorem randomScanGibbs_expectation_sum
    (L : FiniteOrientedLatticeWilsonSystem)
    {ι : Type*} [Fintype ι]
    (u : ι → L.Configuration → ℝ) :
    L.gibbsExpectationReal (fun A => ∑ i : ι, u i A) =
      ∑ i : ι, L.gibbsExpectationReal (u i) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  calc
    (∑ A : L.Configuration,
      L.gibbsProbabilityReal A * ∑ i : ι, u i A) =
        ∑ A : L.Configuration,
          ∑ i : ι, L.gibbsProbabilityReal A * u i A := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
    _ = ∑ i : ι,
        ∑ A : L.Configuration,
          L.gibbsProbabilityReal A * u i A := by
      rw [Finset.sum_comm]

/-- A single exact physical-link heat-bath conditional average preserves Gibbs
expectation.  The proof reuses the established Gibbs-pairing symmetry rather
than re-proving detailed balance. -/
theorem finite_oriented_singleLinkConditionalAverage_gibbsExpectationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (target : L.Edge) :
    L.gibbsExpectationReal
        (fun A => L.singleLinkConditionalAverage f A target) =
      L.gibbsExpectationReal f := by
  have hOne :
      L.singleLinkHeatBathProjection target
          (fun _ : L.Configuration => (1 : ℝ)) =
        (fun _ : L.Configuration => (1 : ℝ)) := by
    apply finite_oriented_singleLinkHeatBathProjection_fixes
    intro A B _hAgree
    rfl
  calc
    L.gibbsExpectationReal
        (fun A => L.singleLinkConditionalAverage f A target) =
      L.gibbsPairingReal
        (L.singleLinkHeatBathProjection target f)
        (fun _ : L.Configuration => (1 : ℝ)) := by
          rw [randomScanGibbs_singleLinkAverage_eq_projection]
          exact (randomScanGibbs_pairing_one_right
            L (L.singleLinkHeatBathProjection target f)).symm
    _ = L.gibbsPairingReal f
        (L.singleLinkHeatBathProjection target
          (fun _ : L.Configuration => (1 : ℝ))) :=
      finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
        L target f (fun _ : L.Configuration => (1 : ℝ))
    _ = L.gibbsPairingReal f
        (fun _ : L.Configuration => (1 : ℝ)) := by
      rw [hOne]
    _ = L.gibbsExpectationReal f :=
      randomScanGibbs_pairing_one_right L f

/-- The uniform random-scan conditional average preserves Gibbs expectation on
a nonempty physical-link carrier. -/
theorem finite_oriented_randomScanConditionalAverage_gibbsExpectationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hEdge : 0 < Fintype.card L.Edge) :
    L.gibbsExpectationReal (L.randomScanConditionalAverage f) =
      L.gibbsExpectationReal f := by
  have hCardNeNat : Fintype.card L.Edge ≠ 0 := Nat.ne_of_gt hEdge
  have hCardNeReal : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast hCardNeNat
  change
    L.gibbsExpectationReal
        (fun A => (Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ target : L.Edge,
            L.singleLinkConditionalAverage f A target) =
      L.gibbsExpectationReal f
  rw [randomScanGibbs_expectation_const_mul,
    randomScanGibbs_expectation_sum]
  simp_rw [finite_oriented_singleLinkConditionalAverage_gibbsExpectationReal]
  simp [hCardNeReal]

/-- Every iterate of the uniform random-scan conditional average preserves the
initial Gibbs expectation. -/
theorem finite_oriented_randomScanConditionalAverageIterate_gibbsExpectationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ) :
    L.gibbsExpectationReal
        (L.randomScanConditionalAverageIterate f k) =
      L.gibbsExpectationReal f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [finite_oriented_randomScanConditionalAverageIterate_succ,
        finite_oriented_randomScanConditionalAverage_gibbsExpectationReal
          L (L.randomScanConditionalAverageIterate f k) hEdge,
        ih]

/-- If an observable differs from its value at `A` by at most `M` at every
configuration, then its value at `A` differs from its Gibbs expectation by at
most `M`. -/
theorem finite_oriented_abs_sub_gibbsExpectationReal_le_of_pairwise
    (L : FiniteOrientedLatticeWilsonSystem)
    (g : L.Configuration → ℝ)
    (A : L.Configuration)
    (M : ℝ)
    (hPair : ∀ B : L.Configuration, |g A - g B| ≤ M) :
    |g A - L.gibbsExpectationReal g| ≤ M := by
  classical
  have hMass :
      (∑ B : L.Configuration, (L.gibbsPMF B).toReal) = 1 :=
    finite_pmf_sum_toReal_eq_one L.gibbsPMF
  have hRewrite :
      g A - L.gibbsExpectationReal g =
        ∑ B : L.Configuration,
          (L.gibbsPMF B).toReal * (g A - g B) := by
    unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
      FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
    calc
      g A - ∑ B : L.Configuration, (L.gibbsPMF B).toReal * g B =
          1 * g A -
            ∑ B : L.Configuration, (L.gibbsPMF B).toReal * g B := by
        ring
      _ = (∑ B : L.Configuration, (L.gibbsPMF B).toReal) * g A -
            ∑ B : L.Configuration, (L.gibbsPMF B).toReal * g B := by
        rw [hMass]
      _ = ∑ B : L.Configuration,
          ((L.gibbsPMF B).toReal * g A -
            (L.gibbsPMF B).toReal * g B) := by
        rw [Finset.sum_mul, Finset.sum_sub_distrib]
      _ = ∑ B : L.Configuration,
          (L.gibbsPMF B).toReal * (g A - g B) := by
        apply Finset.sum_congr rfl
        intro B _hB
        ring
  rw [hRewrite]
  exact finite_pmf_abs_expectation_le_bound
    L.gibbsPMF (fun B => g A - g B) M hPair

/-- The `k`th random-scan observable iterate is within the geometrically
contracted total variation mass of the original Gibbs expectation. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageIterate_abs_sub_gibbsExpectation_le_pow_mul_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ)
    (A : L.Configuration) :
    |L.randomScanConditionalAverageIterate f k A -
        L.gibbsExpectationReal f| ≤
      (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
        ∑ source : L.Edge, P.variation source := by
  have hExpectation :=
    finite_oriented_randomScanConditionalAverageIterate_gibbsExpectationReal
      L f hEdge k
  calc
    |L.randomScanConditionalAverageIterate f k A -
        L.gibbsExpectationReal f| =
      |L.randomScanConditionalAverageIterate f k A -
        L.gibbsExpectationReal
          (L.randomScanConditionalAverageIterate f k)| := by
      rw [hExpectation]
    _ ≤ ∑ source : L.Edge,
        P.randomScanConditionalAverageVariationIterate D k source := by
      apply finite_oriented_abs_sub_gibbsExpectationReal_le_of_pairwise
      intro B
      exact
        P.randomScanConditionalAverageIterate_abs_sub_le_sum_variation
          D k A B
    _ ≤ (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
        ∑ source : L.Edge, P.variation source :=
      P.randomScanConditionalAverageVariationIterate_sum_le_pow D hEdge k

/-- For a selected periodic `Z₂` plaquette observable, every random-scan iterate
is uniformly within `4 q^k` of its original Gibbs expectation. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanObservableIterate_abs_sub_gibbsExpectation_le_four_mul_pow
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (k : ℕ)
    (A :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    |FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverageIterate
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p) k A -
      FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p)| ≤
      4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n) :=
    Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
  have hGeneral :=
    (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
      n beta hBeta p)
      |>.randomScanConditionalAverageIterate_abs_sub_gibbsExpectation_le_pow_mul_sum
        D hEdge k A
  have hInitial :=
    z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile_sum_le_four
      n beta hBeta p
  have hPowNonneg :
      0 ≤ (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k :=
    pow_nonneg
      (finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
        D hEdge) k
  calc
    |FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverageIterate
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p) k A -
      FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) p)| ≤
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
          ∑ source : PeriodicHypercubicEdge n,
            (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
              n beta hBeta p).variation source := hGeneral
    _ ≤ (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k * 4 :=
      mul_le_mul_of_nonneg_left hInitial hPowNonneg
    _ = 4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
      ring

end

end MathlibAnalytic
end MGAP4D
