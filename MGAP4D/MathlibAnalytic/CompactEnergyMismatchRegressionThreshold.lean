import MGAP4D.MathlibAnalytic.CompactEnergyMismatchOptimization
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ACB — signed energy alignment and regression-defect thresholds

For the same continuous physical link receiver, the ACA bound can be
expressed using its genuine energy correlation. Its positive certificate
is controlled by a one-sided regression defect only when the global
energy covariance has the appropriate sign. A wrong orientation gives a
precise obstruction to this positive-slope certificate family.

These scalar lemmas never assume the real Wilson transfer-section
defect is small. They distinguish an exact threshold equivalence,
a sufficient defect estimate, and a necessary orientation condition.
-/

namespace MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

noncomputable section
set_option autoImplicit false

/-- The signed correlation of a receiver with genuine SU(2) energy
Var(E)=1/4. Defined also at variance zero, but its estimates below
are explicitly restricted to positive receiver variance. -/
def energyAlignmentRatio (s v C : ℝ) : ℝ := 2 * s * C / Real.sqrt v

/-- The actual least-squares energy defect in scalar coordinates. -/
def energyRegressionDefect (v C : ℝ) : ℝ := v - 4 * C ^ 2

/-- The correlation ratio lies in [-1,1] by genuine energy Cauchy.
No favorable orientation is assumed. -/
theorem energyAlignmentRatio_bounds (s v C : ℝ)
    (hs : s ^ 2 = 1) (hv : 0 < v) (hC : 4 * C ^ 2 ≤ v) :
    -1 ≤ energyAlignmentRatio s v C ∧ energyAlignmentRatio s v C ≤ 1 := by
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hsq : (2 * s * C) ^ 2 ≤ v := by
    calc
      _ = 4 * s ^ 2 * C ^ 2 := by ring
      _ = 4 * C ^ 2 := by rw [hs]; ring
      _ ≤ v := hC
  have hAbs := abs_le.mp (Real.abs_le_sqrt hsq)
  unfold energyAlignmentRatio
  constructor
  · apply (le_div_iff₀ hσ).mpr
    nlinarith [hAbs.1]
  · apply (div_le_iff₀ hσ).mpr
    nlinarith [hAbs.2]

/-- Exact normalized defect identity: nonzero energy variance is
already incorporated into the numerical factor four. -/
theorem energyAlignmentRatio_defect_identity (s v C : ℝ)
    (hs : s ^ 2 = 1) (hv : 0 < v) :
    1 - energyAlignmentRatio s v C ^ 2 = energyRegressionDefect v C / v := by
  unfold energyAlignmentRatio energyRegressionDefect
  rw [div_pow, Real.sq_sqrt hv.le]
  have hsq : (2 * s * C) ^ 2 = 4 * C ^ 2 := by
    calc
      _ = 4 * s ^ 2 * C ^ 2 := by ring
      _ = 4 * C ^ 2 := by rw [hs]; ring
  rw [hsq]
  field_simp [hv.ne']
  ring

/-- Exactly factor the same ACA optimized full-mismatch budget
through the signed energy correlation. -/
theorem optimizedTransferBudget_eq_alignment (b P s v C : ℝ) (hv : 0 < v) :
    b * P * (Real.sqrt v - 2 * s * C) =
      b * P * Real.sqrt v * (1 - energyAlignmentRatio s v C) := by
  unfold energyAlignmentRatio
  have hσ : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  field_simp [hσ]
  ring

/-- The ACA strict certificate is exactly a normalized alignment
threshold when coupling, Perron prefactor and variance are positive. -/
theorem optimizedTransferBudget_lt_iff_alignment (b P s v C T : ℝ)
    (hb : 0 < b) (hP : 0 < P) (hv : 0 < v) :
    b * P * (Real.sqrt v - 2 * s * C) < T ↔
      1 - energyAlignmentRatio s v C < T / (b * P * Real.sqrt v) := by
  rw [optimizedTransferBudget_eq_alignment b P s v C hv]
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hcoef : 0 < b * P * Real.sqrt v := mul_pos (mul_pos hb hP) hσ
  constructor
  · intro h
    apply (lt_div_iff₀ hcoef).mpr
    convert h using 1 <;> ring
  · intro h
    have ht := (lt_div_iff₀ hcoef).mp h
    convert ht using 1 <;> ring

/-- With favorable signed covariance, the scaled optimal budget is
bounded by the true energy regression defect. No smallness hypothesis. -/
theorem optimizedTransferBudget_mul_stddev_le_defect (b P s v C : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P) (hv : 0 < v) (hs : s ^ 2 = 1)
    (hC : 4 * C ^ 2 ≤ v) (hdir : 0 ≤ s * C) :
    (b * P * (Real.sqrt v - 2 * s * C)) * Real.sqrt v ≤
      b * P * energyRegressionDefect v C := by
  let σ : ℝ := Real.sqrt v
  let q : ℝ := 2 * s * C
  have hσsq : σ ^ 2 = v := Real.sq_sqrt hv.le
  have hqsq : q ^ 2 = 4 * C ^ 2 := by
    dsimp [q]
    calc
      _ = 4 * s ^ 2 * C ^ 2 := by ring
      _ = 4 * C ^ 2 := by rw [hs]; ring
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hqle : q ≤ σ := by
    have hsq : q ^ 2 ≤ v := by rw [hqsq]; exact hC
    exact Real.le_sqrt_of_sq_le hsq
  have hprod : 0 ≤ q * (σ - q) := mul_nonneg hq (sub_nonneg.mpr hqle)
  have hbasic : (σ - q) * σ ≤ v - 4 * C ^ 2 := by
    rw [← hσsq, ← hqsq]
    nlinarith [hprod]
  change (b * P * (σ - q)) * σ ≤ b * P * (v - 4 * C ^ 2)
  calc
    _ = (b * P) * ((σ - q) * σ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbasic (mul_nonneg hb hP)

/-- An independently verified small regression defect and the correct
covariance direction suffice for an ACA positive certificate. -/
theorem smallDefect_implies_optimizedTransferBudget_lt (b P s v C T : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P) (hv : 0 < v) (hs : s ^ 2 = 1)
    (hC : 4 * C ^ 2 ≤ v) (hdir : 0 ≤ s * C)
    (hsmall : b * P * energyRegressionDefect v C < T * Real.sqrt v) :
    b * P * (Real.sqrt v - 2 * s * C) < T := by
  have hbound := optimizedTransferBudget_mul_stddev_le_defect b P s v C
    hb hP hv hs hC hdir
  have hσ : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  exact (mul_lt_mul_right hσ).mp (hbound.trans_lt hsmall)

/-- Wrong global covariance direction keeps the same positive-slope
budget above the uncorrected standard-deviation scale. -/
theorem wrongOrientation_budget_ge_baseline (b P s v C : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P) (hdir : s * C ≤ 0) :
    b * P * Real.sqrt v ≤ b * P * (Real.sqrt v - 2 * s * C) := by
  apply mul_le_mul_of_nonneg_left (show Real.sqrt v ≤ Real.sqrt v - 2 * s * C by
    linarith) (mul_nonneg hb hP)

/-- When the positive-event threshold is no larger than the bare
standard-deviation scale, a strictly positive certificate requires
a strictly favorable covariance orientation. -/
theorem positiveCertificate_forces_favorableOrientation (b P s v C T : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P)
    (hbase : T ≤ b * P * Real.sqrt v)
    (hcert : b * P * (Real.sqrt v - 2 * s * C) < T) :
    0 < s * C := by
  by_contra hn
  have hbad : s * C ≤ 0 := le_of_not_gt hn
  have hge := wrongOrientation_budget_ge_baseline b P s v C hb hP hbad
  exact (not_lt_of_ge (hbase.trans hge)) hcert

end MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment

#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.energyAlignmentRatio_bounds
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.energyAlignmentRatio_defect_identity
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimizedTransferBudget_eq_alignment
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimizedTransferBudget_lt_iff_alignment
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.optimizedTransferBudget_mul_stddev_le_defect
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.smallDefect_implies_optimizedTransferBudget_lt
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.wrongOrientation_budget_ge_baseline
#print axioms MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment.positiveCertificate_forces_favorableOrientation
