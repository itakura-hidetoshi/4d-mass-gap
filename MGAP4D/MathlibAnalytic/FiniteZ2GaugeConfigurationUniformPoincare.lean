import MGAP4D.MathlibAnalytic.FiniteZ2TensorProductUniformPoincareTransfer
import MGAP4D.MathlibAnalytic.Z2WilsonTemporalCrossingUniformConstants
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The actual two-point gauge group inherits its finite enumeration from
`Bool`. -/
noncomputable local instance z2GaugeFintype : Fintype Z2Gauge :=
  Fintype.ofEquiv Bool boolEquivZ2Gauge

/-- Canonical finite relabelling of a `Z₂` configuration space as a Boolean
cube. -/
noncomputable def finiteZ2GaugeConfigurationEquiv
    (ι : Type) [Fintype ι] :
    (ι → Z2Gauge) ≃
      (Fin (Fintype.card ι) → Bool) where
  toFun A i := boolEquivZ2Gauge.symm (A ((Fintype.equivFin ι).symm i))
  invFun b e := boolEquivZ2Gauge (b (Fintype.equivFin ι e))
  left_inv := by
    intro A
    funext e
    simp
  right_inv := by
    intro b
    funext i
    simp

/-- The dimension-free normalized crossing kernel on an arbitrary finite set
of actual `Z₂` gauge links. -/
def finiteZ2GaugeNormalizedProductKernel
    (q : ℝ) (ι : Type) [Fintype ι] :
    (ι → Z2Gauge) → (ι → Z2Gauge) → ℝ :=
  fun A B =>
    finiteZ2NormalizedProductKernel q (Fintype.card ι)
      (finiteZ2GaugeConfigurationEquiv ι A)
      (finiteZ2GaugeConfigurationEquiv ι B)

/-- The transported actual-carrier kernel remains symmetric. -/
theorem finiteZ2GaugeNormalizedProductKernel_symmetric
    (q : ℝ) (ι : Type) [Fintype ι]
    (A B : ι → Z2Gauge) :
    finiteZ2GaugeNormalizedProductKernel q ι A B =
      finiteZ2GaugeNormalizedProductKernel q ι B A := by
  exact finiteZ2NormalizedProductKernel_symmetric q _ _ _

/-- Reindexing identifies the actual-carrier quadratic form with the Boolean
cube quadratic form exactly. -/
theorem finiteZ2GaugeNormalizedProductKernel_quadratic_equiv
    (q : ℝ) (ι : Type) [Fintype ι]
    (f : (ι → Z2Gauge) → ℝ) :
    finiteFunctionKernelQuadratic
        (finiteZ2GaugeNormalizedProductKernel q ι) f =
      finiteFunctionKernelQuadratic
        (finiteZ2NormalizedProductKernel q (Fintype.card ι))
        (fun b => f ((finiteZ2GaugeConfigurationEquiv ι).symm b)) := by
  rw [finiteFunctionKernelQuadratic_equiv
    (finiteZ2GaugeConfigurationEquiv ι)
    (finiteZ2GaugeNormalizedProductKernel q ι) f]
  rfl

/-- Reindexing identifies total mass exactly. -/
theorem finiteZ2GaugeConfiguration_mass_equiv
    (ι : Type) [Fintype ι]
    (f : (ι → Z2Gauge) → ℝ) :
    finiteFunctionMass f =
      finiteFunctionMass
        (fun b => f ((finiteZ2GaugeConfigurationEquiv ι).symm b)) :=
  finiteFunctionMass_equiv (finiteZ2GaugeConfigurationEquiv ι) f

/-- Reindexing identifies the squared Euclidean norm exactly. -/
theorem finiteZ2GaugeConfiguration_normSq_equiv
    (ι : Type) [Fintype ι]
    (f : (ι → Z2Gauge) → ℝ) :
    finiteFunctionNormSq f =
      finiteFunctionNormSq
        (fun b => f ((finiteZ2GaugeConfigurationEquiv ι).symm b)) :=
  finiteFunctionNormSq_equiv (finiteZ2GaugeConfigurationEquiv ι) f

/-- Every mean-zero actual `Z₂` configuration function contracts by the same
local sign-mode rate, independently of the finite link set. -/
theorem finiteZ2GaugeNormalizedProductKernel_quadratic_le_q_mul_of_mass_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι]
    (f : (ι → Z2Gauge) → ℝ)
    (hmass : finiteFunctionMass f = 0) :
    finiteFunctionKernelQuadratic
        (finiteZ2GaugeNormalizedProductKernel q ι) f ≤
      q * finiteFunctionNormSq f := by
  let g : (Fin (Fintype.card ι) → Bool) → ℝ :=
    fun b => f ((finiteZ2GaugeConfigurationEquiv ι).symm b)
  have hmassg : finiteFunctionMass g = 0 := by
    rw [← finiteZ2GaugeConfiguration_mass_equiv ι f]
    exact hmass
  have hbound :=
    finiteZ2NormalizedProductKernel_quadratic_le_q_mul_of_mass_zero
      hq0 hq1 (Fintype.card ι) g hmassg
  rw [finiteZ2GaugeNormalizedProductKernel_quadratic_equiv]
  rw [finiteZ2GaugeConfiguration_normSq_equiv] at hbound ⊢
  exact hbound

/-- Hilbert-space Rayleigh contraction on an arbitrary finite actual `Z₂`
configuration space. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_rayleigh_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι]
    (f : FiniteBoundaryHilbert (ι → Z2Gauge))
    (hmass : finiteFunctionMass f = 0) :
    inner ℝ
        (finiteKernelOperator
          (finiteZ2GaugeNormalizedProductKernel q ι) f) f ≤
      q * ‖f‖ ^ 2 := by
  rw [← finiteFunctionKernelQuadratic_eq_inner_operator,
    ← finiteFunctionNormSq_eq_norm_sq]
  exact finiteZ2GaugeNormalizedProductKernel_quadratic_le_q_mul_of_mass_zero
    hq0 hq1 ι f hmass

/-- Volume-independent Poincare coercivity on any finite actual `Z₂`
configuration space. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_poincare
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ι : Type) [Fintype ι]
    (f : FiniteBoundaryHilbert (ι → Z2Gauge))
    (hmass : finiteFunctionMass f = 0) :
    (1 - q) * ‖f‖ ^ 2 ≤
      inner ℝ
        (f - finiteKernelOperator
          (finiteZ2GaugeNormalizedProductKernel q ι) f) f := by
  have hrayleigh :=
    finiteZ2GaugeNormalizedProductKernel_operator_rayleigh_le
      hq0 hq1 ι f hmass
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

end

end MathlibAnalytic
end MGAP4D
