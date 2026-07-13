import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelIndicatorLocalization
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Scalar spectral multiplier for the positive-time Hamiltonian difference
quotient. -/
def pvmSemigroupDifferenceQuotientScalar (t energy : ℝ) : ℝ :=
  (1 - Real.exp (-t * energy)) / t

/-- For fixed time, the scalar semigroup difference quotient is continuous in
energy. -/
theorem continuous_pvmSemigroupDifferenceQuotientScalar (t : ℝ) :
    Continuous (fun energy : ℝ =>
      pvmSemigroupDifferenceQuotientScalar t energy) := by
  unfold pvmSemigroupDifferenceQuotientScalar
  fun_prop

/-- On nonnegative energies and positive times, the semigroup difference quotient
coefficient is nonnegative. -/
theorem pvmSemigroupDifferenceQuotientScalar_nonneg
    {t energy : ℝ} (ht : 0 < t) (henergy : 0 ≤ energy) :
    0 ≤ pvmSemigroupDifferenceQuotientScalar t energy := by
  unfold pvmSemigroupDifferenceQuotientScalar
  have hExp : Real.exp (-t * energy) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  exact div_nonneg (sub_nonneg.mpr hExp) ht.le

/-- The positive-time semigroup difference quotient coefficient is bounded above
by the energy. -/
theorem pvmSemigroupDifferenceQuotientScalar_le_energy
    {t energy : ℝ} (ht : 0 < t) :
    pvmSemigroupDifferenceQuotientScalar t energy ≤ energy := by
  unfold pvmSemigroupDifferenceQuotientScalar
  apply (div_le_iff₀ ht).2
  have hExp := Real.add_one_le_exp (-t * energy)
  nlinarith

/-- Multiplication by an arbitrary scalar preserves the canonical domination by
`energy * value` on the nonnegative spectral half-line. -/
theorem pvmSemigroupDifferenceQuotientScalar_mul_norm_le
    {t energy value : ℝ} (ht : 0 < t) (henergy : 0 ≤ energy) :
    ‖pvmSemigroupDifferenceQuotientScalar t energy * value‖ ≤
      ‖energy * value‖ := by
  have hqNonneg :=
    pvmSemigroupDifferenceQuotientScalar_nonneg ht henergy
  have hqLe :=
    pvmSemigroupDifferenceQuotientScalar_le_energy
      (energy := energy) ht
  calc
    ‖pvmSemigroupDifferenceQuotientScalar t energy * value‖ =
        pvmSemigroupDifferenceQuotientScalar t energy * ‖value‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hqNonneg]
    _ ≤ energy * ‖value‖ :=
      mul_le_mul_of_nonneg_right hqLe (norm_nonneg value)
    _ = ‖energy * value‖ := by
      rw [norm_mul, norm_of_nonneg henergy]

/-- A second-order exponential remainder gives an explicit first-order error
bound for the spectral difference quotient. -/
theorem pvmSemigroupDifferenceQuotientScalar_sub_energy_abs_le
    {t energy : ℝ} (ht : 0 < t) (hsmall : |t * energy| ≤ 1) :
    |pvmSemigroupDifferenceQuotientScalar t energy - energy| ≤
      t * energy ^ 2 := by
  have hTaylor :=
    Real.abs_exp_sub_one_sub_id_le
      (x := -t * energy) (by simpa [abs_neg] using hsmall)
  have hIdentity :
      pvmSemigroupDifferenceQuotientScalar t energy - energy =
        -(Real.exp (-t * energy) - 1 - (-t * energy)) / t := by
    unfold pvmSemigroupDifferenceQuotientScalar
    field_simp [ht.ne']
    ring
  rw [hIdentity, abs_div, abs_neg, abs_of_pos ht]
  calc
    |Real.exp (-t * energy) - 1 - (-t * energy)| / t ≤
        (-t * energy) ^ 2 / t :=
      (div_le_div_iff_of_pos_right ht).2 hTaylor
    _ = t * energy ^ 2 := by
      field_simp [ht.ne']

/-- On a fixed nonnegative compact energy window, multiplication by any bounded
Borel function converges uniformly to the Hamiltonian coordinate multiplier. -/
theorem pvmSemigroupDifferenceQuotientScalar_mul_uniformOn_nonnegativeWindow
    (f : PVMBoundedBorelRealFunction)
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < t → t < δ →
          ∀ energy : ℝ, energy ∈ Set.Icc (0 : ℝ) R →
            ‖pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy -
                energy * f.toFun energy‖ < ε := by
  intro ε hε
  obtain ⟨B, hB⟩ := f.bounded_toFun
  have hBnonneg : 0 ≤ B :=
    le_trans (norm_nonneg (f.toFun 0)) (hB 0)
  let a : ℝ := 1 / (R + 1)
  let D : ℝ := R ^ 2 * (B + 1) + 1
  let b : ℝ := ε / D
  let δ : ℝ := min a b
  have hROne : 0 < R + 1 := by linarith
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [sq_nonneg R]
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos hε hD
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min ha hb
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ energy henergy
  have henergyNonneg : 0 ≤ energy := henergy.1
  have henergyR : energy ≤ R := henergy.2
  have htA : t ≤ a := by
    exact (le_of_lt htδ).trans (min_le_left a b)
  have htB : t < b := by
    exact htδ.trans_le (min_le_right a b)
  have hFrac : a * R ≤ 1 := by
    dsimp [a]
    rw [one_div, inv_mul_eq_div]
    exact (div_le_one hROne).2 (by linarith)
  have hmul : t * energy ≤ a * R := by
    exact mul_le_mul htA henergyR henergyNonneg ha.le
  have hsmall : |t * energy| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.le henergyNonneg)]
    exact hmul.trans hFrac
  have hScalar :=
    pvmSemigroupDifferenceQuotientScalar_sub_energy_abs_le ht hsmall
  have hEnergySq : energy ^ 2 ≤ R ^ 2 := by
    nlinarith
  have hFirst :
      ‖pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy -
          energy * f.toFun energy‖ ≤
        (t * energy ^ 2) * B := by
    rw [← sub_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul hScalar (hB energy)
      (norm_nonneg (f.toFun energy))
      (mul_nonneg ht.le (sq_nonneg energy))
  have hSecond :
      (t * energy ^ 2) * B ≤ t * R ^ 2 * (B + 1) := by
    calc
      (t * energy ^ 2) * B ≤ (t * R ^ 2) * B := by
        gcongr
      _ ≤ (t * R ^ 2) * (B + 1) := by
        gcongr
        linarith
      _ = t * R ^ 2 * (B + 1) := by ring
  have hThird : t * R ^ 2 * (B + 1) < t * D := by
    dsimp [D]
    nlinarith [mul_nonneg ht.le (sq_nonneg R), hBnonneg]
  have hFourth : t * D < ε := by
    have := (lt_div_iff₀ hD).1 (by simpa [b] using htB)
    exact this
  exact hFirst.trans_lt (hSecond.trans_lt (hThird.trans hFourth))

/-- Filter form of uniform convergence on a nonnegative compact energy window. -/
theorem pvmSemigroupDifferenceQuotientScalar_mul_eventually_uniformOn_nonnegativeWindow
    (f : PVMBoundedBorelRealFunction)
    (R : ℝ) (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ energy : ℝ, energy ∈ Set.Icc (0 : ℝ) R →
        ‖pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy -
            energy * f.toFun energy‖ < ε := by
  obtain ⟨δ, hδ, hUniform⟩ :=
    pvmSemigroupDifferenceQuotientScalar_mul_uniformOn_nonnegativeWindow
      f R hR ε hε
  have hBall : Metric.ball (0 : ℝ) δ ∈ nhdsWithin 0 (Set.Ioi 0) :=
    (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
      (Metric.ball_mem_nhds 0 hδ)
  filter_upwards [self_mem_nhdsWithin, hBall] with t ht htdist
  have htPos : 0 < t := by simpa using ht
  have htδ : t < δ := by
    rw [Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs, abs_of_pos htPos] at htdist
    exact htdist
  exact hUniform t htPos htδ

/-- The bounded target Hamiltonian multiplier restricted to the physical
nonnegative spectral half-line. -/
def pvmPositiveEnergyRestrict
    (h : PVMBoundedBorelRealFunction) : PVMBoundedBorelRealFunction :=
  pvmBoundedBorelRestrict (Set.Ici (0 : ℝ)) measurableSet_Ici h

/-- A globally bounded positive-energy semigroup difference-quotient multiplier.

For positive time it is the actual quotient coefficient times `f` on
nonnegative energies and zero on negative energies. At nonpositive time it is
set equal to the positive-energy target, which makes it a total filter-indexed
family without changing the right-hand germ. -/
noncomputable def pvmPositiveSemigroupDifferenceQuotientMultiplier
    (t : ℝ)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy) :
    PVMBoundedBorelRealFunction := by
  classical
  by_cases ht : 0 < t
  · exact
      { toFun := fun energy =>
          if 0 ≤ energy then
            pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy
          else 0
        measurable_toFun := by
          have hq : Measurable (fun energy : ℝ =>
              pvmSemigroupDifferenceQuotientScalar t energy) :=
            (continuous_pvmSemigroupDifferenceQuotientScalar t).measurable
          exact Measurable.ite measurableSet_Ici
            (hq.mul f.measurable_toFun) measurable_const
        bounded_toFun := by
          obtain ⟨C, hC⟩ := h.bounded_toFun
          have hCnonneg : 0 ≤ C :=
            le_trans (norm_nonneg (h.toFun 0)) (hC 0)
          refine ⟨C, ?_⟩
          intro energy
          by_cases henergy : 0 ≤ energy
          · simp only [henergy, if_true]
            calc
              ‖pvmSemigroupDifferenceQuotientScalar t energy *
                  f.toFun energy‖ ≤ ‖energy * f.toFun energy‖ :=
                pvmSemigroupDifferenceQuotientScalar_mul_norm_le ht henergy
              _ = ‖h.toFun energy‖ := by rw [hCoordinate energy]
              _ ≤ C := hC energy
          · simp [henergy, hCnonneg] }
  · exact pvmPositiveEnergyRestrict h

@[simp] theorem pvmPositiveSemigroupDifferenceQuotientMultiplier_apply_of_pos
    {t : ℝ} (ht : 0 < t)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    {energy : ℝ} (henergy : 0 ≤ energy) :
    (pvmPositiveSemigroupDifferenceQuotientMultiplier
      t f h hCoordinate).toFun energy =
      pvmSemigroupDifferenceQuotientScalar t energy * f.toFun energy := by
  classical
  simp [pvmPositiveSemigroupDifferenceQuotientMultiplier, ht, henergy]

@[simp] theorem pvmPositiveSemigroupDifferenceQuotientMultiplier_apply_of_neg
    {t : ℝ} (ht : 0 < t)
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    {energy : ℝ} (henergy : energy < 0) :
    (pvmPositiveSemigroupDifferenceQuotientMultiplier
      t f h hCoordinate).toFun energy = 0 := by
  classical
  simp [pvmPositiveSemigroupDifferenceQuotientMultiplier, ht,
    not_le.mpr henergy]

/-- The total bounded multiplier family converges uniformly to the positive-energy
target on every symmetric compact energy window. -/
theorem pvmPositiveSemigroupDifferenceQuotientMultiplier_eventually_uniformOn_energyWindow
    (f h : PVMBoundedBorelRealFunction)
    (hCoordinate : ∀ energy : ℝ,
      h.toFun energy = energy * f.toFun energy)
    (R : ℝ) (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ energy : ℝ, energy ∈ pvmEnergyWindow R →
        ‖(pvmPositiveSemigroupDifferenceQuotientMultiplier
              t f h hCoordinate).toFun energy -
            (pvmPositiveEnergyRestrict h).toFun energy‖ < ε := by
  filter_upwards
    [self_mem_nhdsWithin,
      pvmSemigroupDifferenceQuotientScalar_mul_eventually_uniformOn_nonnegativeWindow
        f R hR hε] with t ht hUniform
  have htPos : 0 < t := by simpa using ht
  intro energy henergy
  have henergyUpper : energy ≤ R := henergy.2
  by_cases henergyNonneg : 0 ≤ energy
  · have hLocal := hUniform energy ⟨henergyNonneg, henergyUpper⟩
    simpa [pvmPositiveEnergyRestrict, pvmBoundedBorelRestrict,
      pvmPositiveSemigroupDifferenceQuotientMultiplier,
      htPos, henergyNonneg, hCoordinate energy] using hLocal
  · simp [pvmPositiveEnergyRestrict, pvmBoundedBorelRestrict,
      pvmPositiveSemigroupDifferenceQuotientMultiplier,
      htPos, henergyNonneg, hε]

end

end MathlibAnalytic
end MGAP4D
