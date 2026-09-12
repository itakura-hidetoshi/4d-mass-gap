import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

/-- A canonical positive comparison width shrinking to zero. -/
def reciprocalPositiveWidth (n : ℕ) : NNReal :=
  ((n : NNReal) + 1)⁻¹

/-- Every canonical reciprocal width is strictly positive. -/
theorem reciprocalPositiveWidth_pos (n : ℕ) :
    0 < reciprocalPositiveWidth n := by
  exact inv_pos.mpr (by positivity)

/-- The canonical reciprocal widths converge to zero in the ordinary topology. -/
theorem reciprocalPositiveWidth_tendsto_zero_nhds :
    Tendsto reciprocalPositiveWidth atTop (nhds 0) := by
  simpa [reciprocalPositiveWidth] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal))

/-- The canonical reciprocal widths converge to zero through positive widths. -/
theorem reciprocalPositiveWidth_tendsto_zero :
    Tendsto reciprocalPositiveWidth atTop (nhdsWithin 0 (Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    reciprocalPositiveWidth
    reciprocalPositiveWidth_tendsto_zero_nhds
    (Eventually.of_forall reciprocalPositiveWidth_pos)

/-- Quantitative output of a finite-family positive diagonal selection.

At scale `n`, the selected positive width is smaller than the canonical reciprocal
width and every member of the finite family has defect norm smaller than the same
reciprocal bound. -/
structure FiniteFamilyPositiveDiagonalSelectionData
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    (defect : ℕ → ι → NNReal → E) where
  width : ℕ → NNReal
  width_pos : ∀ n, 0 < width n
  width_lt_reciprocal : ∀ n, width n < reciprocalPositiveWidth n
  defect_norm_lt_reciprocal :
    ∀ n i, ‖defect n i (width n)‖ < (reciprocalPositiveWidth n : ℝ)

namespace FiniteFamilyPositiveDiagonalSelectionData

variable
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    {defect : ℕ → ι → NNReal → E}

/-- Pointwise positive-time convergence for every scale and every member of a
finite family admits one common positive width at each scale, with simultaneous
reciprocal quantitative control. -/
noncomputable def of_tendsto
    (hdefect : ∀ n i,
      Tendsto (defect n i) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    FiniteFamilyPositiveDiagonalSelectionData defect := by
  classical
  have hexists : ∀ n : ℕ, ∃ m : ℕ,
      reciprocalPositiveWidth m < reciprocalPositiveWidth n ∧
        ∀ i, ‖defect n i (reciprocalPositiveWidth m)‖ <
          (reciprocalPositiveWidth n : ℝ) := by
    intro n
    have hsmall :
        ∀ᶠ m : ℕ in atTop,
          reciprocalPositiveWidth m < reciprocalPositiveWidth n :=
      (tendsto_order.1 reciprocalPositiveWidth_tendsto_zero_nhds).2
        (reciprocalPositiveWidth n) (reciprocalPositiveWidth_pos n)
    have hmember (i : ι) :
        ∀ᶠ m : ℕ in atTop,
          ‖defect n i (reciprocalPositiveWidth m)‖ <
            (reciprocalPositiveWidth n : ℝ) := by
      have hseq :
          Tendsto
            (fun m : ℕ => defect n i (reciprocalPositiveWidth m))
            atTop (nhds 0) :=
        (hdefect n i).comp reciprocalPositiveWidth_tendsto_zero
      have hmetric :=
        (Metric.tendsto_nhds.mp hseq)
          (reciprocalPositiveWidth n : ℝ)
          (by exact_mod_cast reciprocalPositiveWidth_pos n)
      simpa only [dist_zero_right] using hmetric
    have hallOn : ∀ s : Finset ι,
        ∀ᶠ m : ℕ in atTop,
          ∀ i ∈ s,
            ‖defect n i (reciprocalPositiveWidth m)‖ <
              (reciprocalPositiveWidth n : ℝ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          filter_upwards [hmember a, ih] with m hma hms
          intro i hi
          rcases Finset.mem_insert.mp hi with hia | his
          · simpa [hia] using hma
          · exact hms i his
    have hall :
        ∀ᶠ m : ℕ in atTop,
          ∀ i,
            ‖defect n i (reciprocalPositiveWidth m)‖ <
              (reciprocalPositiveWidth n : ℝ) := by
      filter_upwards [hallOn Finset.univ] with m hm
      intro i
      exact hm i (Finset.mem_univ i)
    exact (hsmall.and hall).exists
  let selectedIndex : ℕ → ℕ := fun n => Classical.choose (hexists n)
  refine
    { width := fun n => reciprocalPositiveWidth (selectedIndex n)
      width_pos := fun n => reciprocalPositiveWidth_pos (selectedIndex n)
      width_lt_reciprocal := fun n => (Classical.choose_spec (hexists n)).1
      defect_norm_lt_reciprocal := ?_ }
  intro n i
  exact (Classical.choose_spec (hexists n)).2 i

/-- Every selected diagonal width sequence converges to zero in the ordinary
`NNReal` topology. -/
theorem width_tendsto_zero_nhds
    (R : FiniteFamilyPositiveDiagonalSelectionData defect) :
    Tendsto R.width atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge (zero_le a) ha).elim
  · intro b hb
    have hbase :=
      (tendsto_order.1 reciprocalPositiveWidth_tendsto_zero_nhds).2 b hb
    filter_upwards [hbase] with n hn
    exact lt_trans (R.width_lt_reciprocal n) hn

/-- Every selected diagonal width sequence shrinks to zero through strictly
positive widths. -/
theorem width_tendsto_zero
    (R : FiniteFamilyPositiveDiagonalSelectionData defect) :
    Tendsto R.width atTop (nhdsWithin 0 (Ioi 0)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    R.width R.width_tendsto_zero_nhds
    (Eventually.of_forall R.width_pos)

/-- Every member of the finite family tends to zero along the common selected
positive diagonal width sequence. -/
theorem defect_tendsto_zero
    (R : FiniteFamilyPositiveDiagonalSelectionData defect)
    (i : ι) :
    Tendsto (fun n => defect n i (R.width n)) atTop (nhds 0) := by
  have hbaseReal :
      Tendsto (fun n => (reciprocalPositiveWidth n : ℝ)) atTop (nhds 0) :=
    (continuous_subtype_val.tendsto (0 : NNReal)).comp
      reciprocalPositiveWidth_tendsto_zero_nhds
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hsmall := (tendsto_order.1 hbaseReal).2 epsilon hepsilon
  filter_upwards [hsmall] with n hn
  simpa only [dist_zero_right] using
    lt_trans (R.defect_norm_lt_reciprocal n i) hn

end FiniteFamilyPositiveDiagonalSelectionData

end

end MathlibAnalytic
end MGAP4D
