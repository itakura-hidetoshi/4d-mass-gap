import MGAP4D.MathlibAnalytic.CompactEnergyRegressionContrast
import MGAP4D.MathlibAnalytic.CompactTwoDensitySignedPairing

/-!
# Quantitative energy residual of two normalized continuous density rows

The determinant of the SAME two normalized rows is compared with an energy
difference.  An actual continuous determinant error, bounded pointwise by
`c * |E(y)-E(x)|`, gives an affine-energy contrast variance at most `c^2/4`
when the energy variance is `1/4`.  The energy regression defect obeys the
same bound.  No continuity or measurability of a divided determinant slope
is required, and no residual-smallness hypothesis is introduced.

The factor `1/4` uses the full antisymmetric two-copy structure.  If
`R=P0-P1+a*E`, `A(x,y)=R(x)-R(y)`, and `K` is the determinant error, then
`integral A*K = integral A^2 = 2*Var(R)`.  Integrating `(K-A)^2 >= 0`
therefore gives `2*Var(R) <= integral K^2` without division by a variance.
-/

namespace MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual

open MeasureTheory
open CompactEnergyMismatchMoment
open scoped Topology
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [SecondCountableTopology α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

private theorem ci {β : Type*} [TopologicalSpace β] [MeasurableSpace β]
    [CompactSpace β] [BorelSpace β] (ρ : Measure β) [IsFiniteMeasure ρ]
    {f : β → ℝ} (hf : Continuous f) : Integrable f ρ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A pointwise error bound for the actual normalized-row determinant
controls the actual affine-energy contrast variance with the sharp
antisymmetric factor.  Both signs and all of the auxiliary product law
are retained; the zero-error endpoint requires no division. -/
theorem variance_contrast_add_energy_le
    (P0 P1 E : α → ℝ) (a c : ℝ)
    (h0 : Continuous P0) (h1 : Continuous P1) (hE : Continuous E)
    (h0mass : (∫ x, P0 x ∂μ) = 1) (h1mass : (∫ x, P1 x ∂μ) = 1)
    (hEV : variance μ E = (1 / 4 : ℝ)) (hc : 0 ≤ c)
    (hdet : ∀ x y,
      |P0 x * P1 y - P1 x * P0 y - a * (E y - E x)| ≤
        c * |E y - E x|) :
    variance μ (fun x => P0 x - P1 x + a * E x) ≤ c ^ 2 / 4 := by
  let d : α → ℝ := fun x => P0 x - P1 x
  let R : α → ℝ := fun x => d x + a * E x
  let A : α × α → ℝ := fun w => R w.1 - R w.2
  let C : α × α → ℝ := fun w => E w.2 - E w.1
  let T : α × α → ℝ := fun w => P0 w.1 * P1 w.2 - P1 w.1 * P0 w.2
  let K : α × α → ℝ := fun w => T w - a * C w
  have hd : Continuous d := h0.sub h1
  have hR : Continuous R := hd.add (continuous_const.mul hE)
  have hA : Continuous A := (hR.comp continuous_fst).sub (hR.comp continuous_snd)
  have hC : Continuous C := (hE.comp continuous_snd).sub (hE.comp continuous_fst)
  have hT : Continuous T :=
    ((h0.comp continuous_fst).mul (h1.comp continuous_snd)).sub
      ((h1.comp continuous_fst).mul (h0.comp continuous_snd))
  have hK : Continuous K := hT.sub (continuous_const.mul hC)
  have hdmean : (∫ x, d x ∂μ) = 0 := by
    change (∫ x, P0 x - P1 x ∂μ) = 0
    rw [integral_sub (ci μ h0) (ci μ h1), h0mass, h1mass]
    ring
  have hRd : covariance μ R d = variance μ R - a * covariance μ R E := by
    have h := CompactEnergyRegressionContrast.covariance_sub_mul_right μ R R E a hR hR hE
    have heq : (fun x => R x - a * E x) = d := by
      funext x
      dsimp [R]
      ring
    rw [heq] at h
    exact h
  have hraw : (∫ x, P0 x * R x ∂μ) - (∫ x, P1 x * R x ∂μ) =
      covariance μ R d := by
    have h0RI : Integrable (fun x : α => P0 x * R x) μ := ci μ (h0.mul hR)
    have h1RI : Integrable (fun x : α => P1 x * R x) μ := ci μ (h1.mul hR)
    unfold covariance
    rw [hdmean, mul_zero, sub_zero]
    rw [← integral_sub h0RI h1RI]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [d]
    ring
  have hAT : (∫ w : α × α, A w * T w ∂μ.prod μ) =
      2 * (variance μ R - a * covariance μ R E) := by
    have h := integral_twoDensitySignedPair_eq_two_mul_gap μ P0 P1 R
      h0 h1 hR h0mass h1mass
    change (∫ w : α × α, A w * T w ∂μ.prod μ) = _ at h
    rw [hraw, hRd] at h
    exact h
  have hAC : (∫ w : α × α, A w * C w ∂μ.prod μ) =
      -2 * covariance μ R E := by
    calc
      _ = ∫ w : α × α,
          -((R w.1 - R w.2) * (E w.1 - E w.2)) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with w
        dsimp [A, C]
        ring
      _ = -(2 * covariance μ R E) := by
        rw [integral_neg, difference_product_integral μ R E hR hE]
      _ = _ := by ring
  have hAK : (∫ w : α × α, A w * K w ∂μ.prod μ) = 2 * variance μ R := by
    calc
      _ = ∫ w : α × α, A w * T w - a * (A w * C w) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with w
        dsimp [K]
        ring
      _ = (∫ w : α × α, A w * T w ∂μ.prod μ) -
          a * ∫ w : α × α, A w * C w ∂μ.prod μ := by
        have hATI : Integrable (fun w : α × α => A w * T w) (μ.prod μ) :=
          ci (μ.prod μ) (hA.mul hT)
        have hACI : Integrable (fun w : α × α => A w * C w) (μ.prod μ) :=
          ci (μ.prod μ) (hA.mul hC)
        have haACI : Integrable (fun w : α × α => a * (A w * C w)) (μ.prod μ) :=
          hACI.const_mul a
        rw [integral_sub hATI haACI, integral_const_mul]
      _ = _ := by rw [hAT, hAC]; ring
  have hASq : (∫ w : α × α, (A w) ^ 2 ∂μ.prod μ) = 2 * variance μ R :=
    difference_square_integral μ R hR
  have hCSq : (∫ w : α × α, (C w) ^ 2 ∂μ.prod μ) = (1 / 2 : ℝ) := by
    have hp (w : α × α) : (C w) ^ 2 = (E w.1 - E w.2) ^ 2 := by
      dsimp [C]
      ring
    simp_rw [hp]
    rw [difference_square_integral μ E hE, hEV]
    norm_num
  have hKPoint (w : α × α) : (K w) ^ 2 ≤ c ^ 2 * (C w) ^ 2 := by
    have h : |K w| ≤ |c| * |C w| := by
      rw [abs_of_nonneg hc]
      exact hdet w.1 w.2
    have hs := pow_le_pow_left₀ (abs_nonneg (K w)) h 2
    simpa only [mul_pow, sq_abs] using hs
  have hKSq : (∫ w : α × α, (K w) ^ 2 ∂μ.prod μ) ≤ c ^ 2 / 2 := by
    have hKI : Integrable (fun w : α × α => (K w) ^ 2) (μ.prod μ) :=
      ci (μ.prod μ) (hK.pow 2)
    have hUI : Integrable (fun w : α × α => c ^ 2 * (C w) ^ 2) (μ.prod μ) :=
      ci (μ.prod μ) (continuous_const.mul (hC.pow 2))
    have h := integral_mono hKI hUI hKPoint
    rw [integral_const_mul, hCSq] at h
    linarith
  have hSquare : (∫ w : α × α, (K w - A w) ^ 2 ∂μ.prod μ) =
      (∫ w : α × α, (K w) ^ 2 ∂μ.prod μ) -
        2 * (∫ w : α × α, A w * K w ∂μ.prod μ) +
          ∫ w : α × α, (A w) ^ 2 ∂μ.prod μ := by
    have hp (w : α × α) : (K w - A w) ^ 2 =
        ((K w) ^ 2 - 2 * (A w * K w)) + (A w) ^ 2 := by ring
    simp_rw [hp]
    have hKI : Integrable (fun w : α × α => (K w) ^ 2) (μ.prod μ) :=
      ci (μ.prod μ) (hK.pow 2)
    have hAI : Integrable (fun w : α × α => (A w) ^ 2) (μ.prod μ) :=
      ci (μ.prod μ) (hA.pow 2)
    have hAKI : Integrable (fun w : α × α => 2 * (A w * K w)) (μ.prod μ) :=
      (ci (μ.prod μ) (hA.mul hK)).const_mul (2 : ℝ)
    have hSub : Integrable (fun w : α × α => (K w) ^ 2 - 2 * (A w * K w))
        (μ.prod μ) := hKI.sub hAKI
    rw [integral_add hSub hAI, integral_sub hKI hAKI,
      integral_const_mul]
  have hn : 0 ≤ ∫ w : α × α, (K w - A w) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [hSquare, hAK, hASq] at hn
  change variance μ R ≤ c ^ 2 / 4
  linarith

/-- The determinant comparison bounds the regression defect together with
the exact square measuring the difference from the chosen energy slope. -/
theorem regressionDefect_add_square_le_of_det_error
    (P0 P1 E : α → ℝ) (a c : ℝ)
    (h0 : Continuous P0) (h1 : Continuous P1) (hE : Continuous E)
    (h0mass : (∫ x, P0 x ∂μ) = 1) (h1mass : (∫ x, P1 x ∂μ) = 1)
    (hEV : variance μ E = (1 / 4 : ℝ)) (hc : 0 ≤ c)
    (hdet : ∀ x y,
      |P0 x * P1 y - P1 x * P0 y - a * (E y - E x)| ≤
        c * |E y - E x|) :
    regressionDefect μ (fun x => P0 x - P1 x) E +
      (a + 4 * covariance μ (fun x => P0 x - P1 x) E) ^ 2 / 4 ≤ c ^ 2 / 4 := by
  have h := variance_contrast_add_energy_le μ P0 P1 E a c
    h0 h1 hE h0mass h1mass hEV hc hdet
  have heq := variance_residual_eq_defect_add_square μ 1 a
    (fun x => P0 x - P1 x) E (h0.sub h1) hE hEV
  simp only [CompactEnergyMismatchMoment.residual, one_mul] at heq
  rw [heq] at h
  exact h

/-- A genuine uniform posterior energy-orthogonal residual estimate from
the two actual normalized density rows and their determinant error. -/
theorem regressionDefect_le_of_det_error
    (P0 P1 E : α → ℝ) (a c : ℝ)
    (h0 : Continuous P0) (h1 : Continuous P1) (hE : Continuous E)
    (h0mass : (∫ x, P0 x ∂μ) = 1) (h1mass : (∫ x, P1 x ∂μ) = 1)
    (hEV : variance μ E = (1 / 4 : ℝ)) (hc : 0 ≤ c)
    (hdet : ∀ x y,
      |P0 x * P1 y - P1 x * P0 y - a * (E y - E x)| ≤
        c * |E y - E x|) :
    regressionDefect μ (fun x => P0 x - P1 x) E ≤ c ^ 2 / 4 := by
  have h := regressionDefect_add_square_le_of_det_error μ P0 P1 E a c
    h0 h1 hE h0mass h1mass hEV hc hdet
  have hs : 0 ≤ (a + 4 * covariance μ (fun x => P0 x - P1 x) E) ^ 2 / 4 := by
    positivity
  linarith

end
end MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual

#print axioms MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual.variance_contrast_add_energy_le
#print axioms MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual.regressionDefect_add_square_le_of_det_error
#print axioms MGAP4D.MathlibAnalytic.CompactPosteriorEnergyResidual.regressionDefect_le_of_det_error
