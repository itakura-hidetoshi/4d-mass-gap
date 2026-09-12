import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanHilbertSpectral
import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteVarianceDirichlet
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Changing only the current value at the resampled coordinate does not
change the one-site conditional expectation. -/
theorem finitePositiveWeightSingleSiteExpectation_update_current
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) :
    finitePositiveWeightSingleSiteExpectation weight f
        (Function.update A e g) e =
      finitePositiveWeightSingleSiteExpectation weight f A e := by
  exact finitePositiveWeightSingleSiteExpectation_eq_of_agreeOff
    weight f (Function.update A e g) A e (by
      intro i hie
      simp [Function.update, hie])

/-- Exact one-site conditional expectation is idempotent. -/
theorem finitePositiveWeightSingleSiteExpectation_idempotent
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    finitePositiveWeightSingleSiteExpectation weight
        (fun B => finitePositiveWeightSingleSiteExpectation weight f B e)
        A e =
      finitePositiveWeightSingleSiteExpectation weight f A e := by
  unfold finitePositiveWeightSingleSiteExpectation
  calc
    (∑ g : G,
      finitePositiveWeightSingleSiteProbability weight A e g *
        finitePositiveWeightSingleSiteExpectation weight f
          (Function.update A e g) e) =
      ∑ g : G,
        finitePositiveWeightSingleSiteProbability weight A e g *
          finitePositiveWeightSingleSiteExpectation weight f A e := by
        apply Finset.sum_congr rfl
        intro g _hg
        rw [finitePositiveWeightSingleSiteExpectation_update_current]
    _ = (∑ g : G,
        finitePositiveWeightSingleSiteProbability weight A e g) *
          finitePositiveWeightSingleSiteExpectation weight f A e := by
        rw [Finset.sum_mul]
    _ = finitePositiveWeightSingleSiteExpectation weight f A e := by
        rw [finitePositiveWeightSingleSiteProbability_sum_eq_one
          weight hweight A e]
        ring

/-- Integrating a one-site conditional expectation against the positive weight
preserves the weighted first moment. -/
theorem finitePositiveWeightSingleSiteExpectation_pairing_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        (fun _ : ι → G => (1 : ℝ)) =
      finitePositiveWeightPairing weight f
        (fun _ : ι → G => (1 : ℝ)) := by
  calc
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        (fun _ : ι → G => (1 : ℝ)) =
      finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight
          (fun _ : ι → G => (1 : ℝ)) A e) :=
      finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f (fun _ : ι → G => (1 : ℝ))
    _ = finitePositiveWeightPairing weight f
        (fun _ : ι → G => (1 : ℝ)) := by
      apply congrArg (finitePositiveWeightPairing weight f)
      funext A
      exact finitePositiveWeightSingleSiteExpectation_one
        weight hweight A e

/-- Idempotence and detailed balance identify the squared norm of a
one-site conditional expectation with its mixed pairing against the original
observable. -/
theorem finitePositiveWeightSingleSiteExpectation_pairing_self
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) =
      finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  calc
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) =
      finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight
          (fun B => finitePositiveWeightSingleSiteExpectation weight f B e)
          A e) :=
      finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
    _ = finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) := by
      apply congrArg (finitePositiveWeightPairing weight f)
      funext A
      exact finitePositiveWeightSingleSiteExpectation_idempotent
        weight hweight f A e
    _ = finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f :=
      finitePositiveWeightPairing_symm weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)

/-- Pairing the pointwise square with the constant-one observable gives the
weighted self-pairing. -/
theorem finitePositiveWeightPairing_sq_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight (fun A => f A ^ 2)
        (fun _ : ι → G => (1 : ℝ)) =
      finitePositiveWeightPairing weight f f := by
  classical
  unfold finitePositiveWeightPairing
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Positive-weight average of the one-site conditional variance at one
coordinate. -/
def finitePositiveWeightIntegratedSingleSiteVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (e : ι) : ℝ :=
  ∑ A : ι → G,
    weight A * finitePositiveWeightSingleSiteVariance weight f A e

/-- Sum of all positive-weight one-site conditional variances. -/
def finitePositiveWeightTotalSingleSiteVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) : ℝ :=
  ∑ e : ι, finitePositiveWeightIntegratedSingleSiteVariance weight f e

/-- The integrated one-site conditional variance is exactly the local
heat-bath pairing defect. -/
theorem finitePositiveWeightIntegratedSingleSiteVariance_eq_pairing_sub
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightIntegratedSingleSiteVariance weight f e =
      finitePositiveWeightPairing weight f f -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  classical
  calc
    finitePositiveWeightIntegratedSingleSiteVariance weight f e =
      finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight
            (fun B => f B ^ 2) A e)
          (fun _ : ι → G => (1 : ℝ)) -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) := by
      unfold finitePositiveWeightIntegratedSingleSiteVariance
        finitePositiveWeightPairing
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro A _hA
      have hVar :=
        finitePositiveWeightSingleSiteVariance_eq_secondMoment_sub_mean_sq
          weight hweight f A e
      change
        finitePositiveWeightSingleSiteVariance weight f A e =
          finitePositiveWeightSingleSiteExpectation weight
              (fun B => f B ^ 2) A e -
            (finitePositiveWeightSingleSiteExpectation weight f A e) ^ 2
        at hVar
      rw [hVar]
      ring
    _ = finitePositiveWeightPairing weight (fun A => f A ^ 2)
          (fun _ : ι → G => (1 : ℝ)) -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
      rw [finitePositiveWeightSingleSiteExpectation_pairing_one
        weight hweight (fun A => f A ^ 2) e,
        finitePositiveWeightSingleSiteExpectation_pairing_self
          weight hweight f e]
    _ = finitePositiveWeightPairing weight f f -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
      rw [finitePositiveWeightPairing_sq_one]

/-- The random-scan mixed pairing is the uniform average of the one-site mixed
pairings. -/
theorem finitePositiveWeightRandomScan_pairing_eq_average_singleSite
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) f =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  let leftPair := finitePositiveWeightPairingLeftLinearMap weight f
  calc
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) f =
      leftPair (finitePositiveWeightRandomScanLinearMap weight f) := by
        rw [finitePositiveWeightRandomScanLinearMap_apply]
        rfl
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (finitePositiveWeightSingleSiteExpectationLinearMap weight e f) f := by
      simp [leftPair, finitePositiveWeightRandomScanLinearMap]
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
      rfl

/-- The total one-site conditional variance is the coordinate count times the
random-scan Dirichlet defect. -/
theorem finitePositiveWeightTotalSingleSiteVariance_eq_card_mul_randomScan_defect
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightTotalSingleSiteVariance weight f =
      (Fintype.card ι : ℝ) *
        (finitePositiveWeightPairing weight f f -
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f) := by
  have hAverage :=
    finitePositiveWeightRandomScan_pairing_eq_average_singleSite weight f
  have hCardNe : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  have hSum :
      (∑ e : ι,
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f) =
        (Fintype.card ι : ℝ) *
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f := by
    field_simp [hCardNe] at hAverage
    nlinarith
  unfold finitePositiveWeightTotalSingleSiteVariance
  simp_rw [finitePositiveWeightIntegratedSingleSiteVariance_eq_pairing_sub
    weight hweight f]
  rw [Finset.sum_sub_distrib]
  have hConst :
      (∑ _e : ι, finitePositiveWeightPairing weight f f) =
        (Fintype.card ι : ℝ) * finitePositiveWeightPairing weight f f := by
    simp [nsmul_eq_mul]
  rw [hConst, hSum]
  ring

/-- Generic Dobrushin approximate tensorization for an arbitrary strictly
positive finite product weight. -/
theorem finitePositiveWeightDobrushin_approximateTensorization
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0) :
    finitePositiveWeightDobrushinHeatBathGap D *
        finitePositiveWeightPairing weight f f ≤
      finitePositiveWeightTotalSingleSiteVariance weight f := by
  have hRayleigh :=
    finitePositiveWeight_centered_randomScan_rayleigh_le_rate
      weight hweight D hCard f hCenter
  have hDefect :
      finitePositiveWeightDobrushinHeatBathGap D /
          (Fintype.card ι : ℝ) *
          finitePositiveWeightPairing weight f f ≤
        finitePositiveWeightPairing weight f f -
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f := by
    unfold finitePositiveWeightDobrushinRandomScanRate at hRayleigh
    nlinarith
  rw [finitePositiveWeightTotalSingleSiteVariance_eq_card_mul_randomScan_defect
    weight hweight hCard f]
  have hCardPos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hCard
  have hCardNe : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hCardPos
  calc
    finitePositiveWeightDobrushinHeatBathGap D *
        finitePositiveWeightPairing weight f f =
      (Fintype.card ι : ℝ) *
        (finitePositiveWeightDobrushinHeatBathGap D /
          (Fintype.card ι : ℝ) *
            finitePositiveWeightPairing weight f f) := by
      field_simp [hCardNe]
    _ ≤ (Fintype.card ι : ℝ) *
        (finitePositiveWeightPairing weight f f -
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f) :=
      mul_le_mul_of_nonneg_left hDefect (le_of_lt hCardPos)

/-- Inverse-gap Poincare form of generic Dobrushin approximate tensorization. -/
theorem finitePositiveWeightDobrushin_pairing_le_inv_gap_mul_totalVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ)
    (hCenter : finitePositiveWeightSum weight f = 0) :
    finitePositiveWeightPairing weight f f ≤
      (finitePositiveWeightDobrushinHeatBathGap D)⁻¹ *
        finitePositiveWeightTotalSingleSiteVariance weight f := by
  have hGap := finitePositiveWeightDobrushinHeatBathGap_pos D
  have hTensor := finitePositiveWeightDobrushin_approximateTensorization
    weight hweight D hCard f hCenter
  calc
    finitePositiveWeightPairing weight f f =
      (finitePositiveWeightDobrushinHeatBathGap D)⁻¹ *
        (finitePositiveWeightDobrushinHeatBathGap D *
          finitePositiveWeightPairing weight f f) := by
      field_simp [ne_of_gt hGap]
    _ ≤ (finitePositiveWeightDobrushinHeatBathGap D)⁻¹ *
        finitePositiveWeightTotalSingleSiteVariance weight f :=
      mul_le_mul_of_nonneg_left hTensor (le_of_lt (inv_pos.mpr hGap))

end

end MathlibAnalytic
end MGAP4D
