import MGAP4D.MathlibAnalytic.PhysicalYangMillsDerivedDiscreteTransferRate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

noncomputable section

open Filter Set Topology

namespace MGAP4D
namespace MathlibAnalytic

/-- Generic conversion from a small positive Dirichlet defect to the logarithmic
one-step transfer rate.

The finite transfer factor is *defined* by

`r_n = sqrt (1 - delta_n)`.

The only asymptotic input is the first-order physical scaling

`delta_n / a_n -> 2 m`.

No Taylor-series coefficient or exact mass value is assumed.  The proof uses
only the elementary logarithm bounds

`log x <= x - 1`,
`1 - x⁻¹ <= log x`

and the squeeze theorem. -/
structure PositiveDirichletDefectScaling
    (latticeSpacing defect : ℕ → ℝ) where
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  defect_nonneg : ∀ n, 0 ≤ defect n
  defect_lt_one : ∀ n, defect n < 1
  mass : ℝ
  mass_pos : 0 < mass
  defectRate_tendsto :
    Tendsto (fun n => defect n / latticeSpacing n) atTop (nhds (2 * mass))

namespace PositiveDirichletDefectScaling

variable {latticeSpacing defect : ℕ → ℝ}

/-- Dimensionful first-order Dirichlet defect rate. -/
def defectRate
    (_A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) : ℝ :=
  defect n / latticeSpacing n

/-- The transfer factor canonically determined by the squared norm defect. -/
def transferFactor
    (_A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) : ℝ :=
  Real.sqrt (1 - defect n)

/-- The logarithmic mass rate associated with the defect-derived factor. -/
def massRate
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) : ℝ :=
  -Real.log (A.transferFactor n) / latticeSpacing n

/-- Lower squeeze rate `delta_n / (2 a_n)`. -/
def lowerRate
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) : ℝ :=
  A.defectRate n / 2

/-- Upper squeeze rate
`delta_n / (2 a_n (1 - delta_n))`. -/
def upperRate
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) : ℝ :=
  (A.defectRate n / 2) * (1 - defect n)⁻¹

/-- Every defect-derived transfer factor is strictly positive. -/
theorem transferFactor_pos
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) :
    0 < A.transferFactor n := by
  rw [transferFactor, Real.sqrt_pos]
  exact sub_pos.mpr (A.defect_lt_one n)

/-- Every defect-derived transfer factor is at most one. -/
theorem transferFactor_le_one
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) :
    A.transferFactor n ≤ 1 := by
  rw [transferFactor, Real.sqrt_le_one]
  linarith [A.defect_nonneg n]

/-- First-order defect scaling and vanishing lattice spacing force the defect
itself to vanish. -/
theorem defect_tendsto_zero
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    Tendsto defect atTop (nhds 0) := by
  have hprod := A.defectRate_tendsto.mul A.latticeSpacing_tendsto_zero
  have heq :
      (fun n => A.defectRate n * latticeSpacing n) = defect := by
    funext n
    unfold defectRate
    field_simp [ne_of_gt (A.latticeSpacing_pos n)]
  rw [← heq]
  simpa using hprod

/-- The lower squeeze rate converges to the continuum mass. -/
theorem lowerRate_tendsto_mass
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    Tendsto A.lowerRate atTop (nhds A.mass) := by
  have h := A.defectRate_tendsto.div_const 2
  simpa [lowerRate, defectRate] using h

/-- The reciprocal correction `(1-delta_n)⁻¹` tends to one. -/
theorem one_sub_defect_inv_tendsto_one
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    Tendsto (fun n => (1 - defect n)⁻¹) atTop (nhds 1) := by
  have hsub :
      Tendsto (fun n => 1 - defect n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub A.defect_tendsto_zero
  simpa using hsub.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- The upper squeeze rate also converges to the continuum mass. -/
theorem upperRate_tendsto_mass
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    Tendsto A.upperRate atTop (nhds A.mass) := by
  have h := A.lowerRate_tendsto_mass.mul A.one_sub_defect_inv_tendsto_one
  simpa [upperRate] using h

/-- Elementary lower logarithmic bound:

`delta_n / (2 a_n) <= -log(sqrt(1-delta_n)) / a_n`. -/
theorem lowerRate_le_massRate
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) :
    A.lowerRate n ≤ A.massRate n := by
  let x := 1 - defect n
  have hx : 0 < x := by
    dsimp [x]
    exact sub_pos.mpr (A.defect_lt_one n)
  have hlog := Real.log_le_sub_one_of_pos hx
  have hnum : defect n / 2 ≤ -Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hx)]
    dsimp [x] at hlog
    linarith
  have hdiv := (div_le_div_iff₀ (A.latticeSpacing_pos n)).2 hnum
  simpa [lowerRate, defectRate, massRate, transferFactor, x] using hdiv

/-- Elementary upper logarithmic bound:

`-log(sqrt(1-delta_n)) / a_n
  <= delta_n / (2 a_n (1-delta_n))`. -/
theorem massRate_le_upperRate
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (n : ℕ) :
    A.massRate n ≤ A.upperRate n := by
  let x := 1 - defect n
  have hx : 0 < x := by
    dsimp [x]
    exact sub_pos.mpr (A.defect_lt_one n)
  have hxne : x ≠ 0 := ne_of_gt hx
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have hneglog : -Real.log x ≤ defect n / x := by
    have heq : x⁻¹ - 1 = defect n / x := by
      dsimp [x]
      field_simp [hxne]
      ring
    calc
      -Real.log x ≤ x⁻¹ - 1 := by linarith
      _ = defect n / x := heq
  have hnum :
      -Real.log (Real.sqrt x) ≤ (defect n / x) / 2 := by
    rw [Real.log_sqrt (le_of_lt hx)]
    linarith
  have hdiv := (div_le_div_iff₀ (A.latticeSpacing_pos n)).2 hnum
  have heq :
      ((defect n / x) / 2) / latticeSpacing n = A.upperRate n := by
    unfold upperRate defectRate
    dsimp [x]
    field_simp [ne_of_gt (A.latticeSpacing_pos n), hxne]
    ring
  rw [heq] at hdiv
  simpa [massRate, transferFactor, x] using hdiv

/-- Squeezing between the two elementary logarithmic bounds converts the
first-order Dirichlet defect scaling into the physical logarithmic mass rate. -/
theorem massRate_tendsto_mass
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    Tendsto A.massRate atTop (nhds A.mass) :=
  A.lowerRate_tendsto_mass.squeeze A.upperRate_tendsto_mass
    (fun n => A.lowerRate_le_massRate n)
    (fun n => A.massRate_le_upperRate n)

/-- Package the defect-derived factor into the generic discrete transfer-rate
spine.  The convergence field is theorem-generated from the Dirichlet scaling,
not separately assumed. -/
noncomputable def toPositiveDiscreteTransferRateLimit
    (A : PositiveDirichletDefectScaling latticeSpacing defect) :
    PositiveDiscreteTransferRateLimit latticeSpacing A.transferFactor where
  latticeSpacing_pos := A.latticeSpacing_pos
  latticeSpacing_tendsto_zero := A.latticeSpacing_tendsto_zero
  transferFactor_pos := A.transferFactor_pos
  transferFactor_le_one := A.transferFactor_le_one
  mass := A.mass
  mass_pos := A.mass_pos
  massRate_tendsto := A.massRate_tendsto_mass

end PositiveDirichletDefectScaling

end MathlibAnalytic
end MGAP4D

end