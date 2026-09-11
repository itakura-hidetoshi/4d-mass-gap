import MGAP4D.MathlibAnalytic.DirichletDefectScalingToDiscreteTransferRate
import Mathlib.Tactic

noncomputable section

open Filter Topology

namespace MGAP4D
namespace MathlibAnalytic

namespace PositiveDirichletDefectScaling

variable {latticeSpacing defect : ℕ → ℝ}

/-- Rescaling the physical Euclidean-time unit by a positive factor `c`
rescales lattice spacing by `c` and the mass extracted from the same intrinsic
Dirichlet defect by the inverse factor `1/c`.

This theorem makes the dimensionful character of the derived mass explicit.
In particular, a bare numerical value cannot be invariant under an unfixed
choice of Euclidean-time units. -/
noncomputable def rescaleTime
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (c : ℝ)
    (hc : 0 < c) :
    PositiveDirichletDefectScaling (fun n => c * latticeSpacing n) defect where
  latticeSpacing_pos := fun n => mul_pos hc (A.latticeSpacing_pos n)
  latticeSpacing_tendsto_zero := by
    simpa using tendsto_const_nhds.mul A.latticeSpacing_tendsto_zero
  defect_nonneg := A.defect_nonneg
  defect_lt_one := A.defect_lt_one
  mass := A.mass / c
  mass_pos := div_pos A.mass_pos hc
  defectRate_tendsto := by
    have hfun :
        (fun n => defect n / (c * latticeSpacing n)) =
          (fun n => (defect n / latticeSpacing n) / c) := by
      funext n
      field_simp [ne_of_gt hc, ne_of_gt (A.latticeSpacing_pos n)]
    rw [hfun]
    convert A.defectRate_tendsto.div_const c using 1 <;> ring

@[simp] theorem rescaleTime_mass
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (c : ℝ)
    (hc : 0 < c) :
    (A.rescaleTime c hc).mass = A.mass / c :=
  rfl

@[simp] theorem rescaleTime_latticeSpacing
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (c : ℝ)
    (hc : 0 < c)
    (n : ℕ) :
    (A.rescaleTime c hc).latticeSpacing_pos n =
      mul_pos hc (A.latticeSpacing_pos n) := by
  rfl

end PositiveDirichletDefectScaling

/-- A positive reference time used only to form a dimensionless mass-time
combination.  This structure does **not** choose a physical normalization: a
model-specific Yang--Mills construction must still supply such a reference
from its own observables/dynamics. -/
structure PositiveReferenceTime where
  value : ℝ
  value_pos : 0 < value

namespace PositiveReferenceTime

/-- A reference time transforms covariantly with a positive rescaling of the
Euclidean-time coordinate. -/
def rescale
    (R : PositiveReferenceTime)
    (c : ℝ)
    (hc : 0 < c) : PositiveReferenceTime where
  value := c * R.value
  value_pos := mul_pos hc R.value_pos

@[simp] theorem rescale_value
    (R : PositiveReferenceTime)
    (c : ℝ)
    (hc : 0 < c) :
    (R.rescale c hc).value = c * R.value :=
  rfl

end PositiveReferenceTime

namespace PositiveDirichletDefectScaling

variable {latticeSpacing defect : ℕ → ℝ}

/-- The dimensionless mass-time product associated with a derived Dirichlet
mass and a positive reference time. -/
def normalizedMass
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (R : PositiveReferenceTime) : ℝ :=
  A.mass * R.value

/-- Simultaneous rescaling of lattice Euclidean time and the reference time
leaves the dimensionless mass-time product invariant.

This is the normalization guardrail for any future exact numerical theorem:
the number must be attached to a model-derived dimensionless quantity, not to
the unfixed bare mass. -/
theorem normalizedMass_rescaleTime
    (A : PositiveDirichletDefectScaling latticeSpacing defect)
    (R : PositiveReferenceTime)
    (c : ℝ)
    (hc : 0 < c) :
    (A.rescaleTime c hc).normalizedMass (R.rescale c hc) =
      A.normalizedMass R := by
  unfold normalizedMass
  simp only [rescaleTime_mass, PositiveReferenceTime.rescale_value]
  field_simp [ne_of_gt hc]

end PositiveDirichletDefectScaling

end MathlibAnalytic
end MGAP4D

end