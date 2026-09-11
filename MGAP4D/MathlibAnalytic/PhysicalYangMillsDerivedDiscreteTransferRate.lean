import MGAP4D.MathlibAnalytic.PhysicalYangMillsFloorExponentialTransferTrajectory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

/-- A positive discrete one-step transfer factor together with a physical
lattice spacing determines its own mass rate

`m_n = - log(r_n) / a_n`.

The continuum rate is therefore a limit extracted from the finite transfer
factors themselves, rather than a numerical value inserted before the finite
Wilson dynamics has been analyzed. -/
structure PositiveDiscreteTransferRateLimit
    (latticeSpacing transferFactor : ℕ → ℝ) where
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0)
  transferFactor_pos : ∀ n, 0 < transferFactor n
  transferFactor_le_one : ∀ n, transferFactor n ≤ 1
  mass : ℝ
  mass_pos : 0 < mass
  massRate_tendsto :
    Tendsto
      (fun n => -Real.log (transferFactor n) / latticeSpacing n)
      atTop (nhds mass)

namespace PositiveDiscreteTransferRateLimit

variable
    {latticeSpacing transferFactor : ℕ → ℝ}

/-- The mass rate directly read from the `n`-th positive transfer factor. -/
def massRate
    (_A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (n : ℕ) : ℝ :=
  -Real.log (transferFactor n) / latticeSpacing n

/-- The supplied convergence field is exactly convergence of the derived mass
rates. -/
theorem derivedMassRate_tendsto
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor) :
    Tendsto A.massRate atTop (nhds A.mass) := by
  simpa only [massRate] using A.massRate_tendsto

/-- Every positive discrete factor is exactly the exponential of its own
derived mass rate times the lattice spacing. -/
theorem factor_eq_exp_neg_massRate_mul_spacing
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (n : ℕ) :
    transferFactor n =
      Real.exp (-A.massRate n * latticeSpacing n) := by
  symm
  unfold massRate
  have hspacing : latticeSpacing n ≠ 0 :=
    ne_of_gt (A.latticeSpacing_pos n)
  have harg :
      -(-Real.log (transferFactor n) / latticeSpacing n) *
          latticeSpacing n =
        Real.log (transferFactor n) := by
    field_simp [hspacing]
  rw [harg, Real.exp_log (A.transferFactor_pos n)]

/-- The floor-selected physical-time factor associated with the scale-dependent
mass rate. -/
def floorFactor
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) (n : ℕ) : ℝ :=
  Real.exp
    (-A.massRate n *
      ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
        latticeSpacing n))

/-- The floor-selected factor is exactly the geometric power of the actual
finite one-step factor. -/
theorem floorFactor_eq_pow
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) (n : ℕ) :
    A.floorFactor t n =
      (transferFactor n) ^
        physicalTemporalFloorNatStep latticeSpacing t n := by
  unfold floorFactor
  symm
  rw [A.factor_eq_exp_neg_massRate_mul_spacing n]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- If the mass rates extracted from the finite factors converge, then the
floor-selected finite decay converges to the continuum exponential with that
**derived** limiting mass. -/
theorem floorFactor_tendsto
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) :
    Tendsto
      (fun n => A.floorFactor t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  have htime :=
    physicalTemporalFloorNatStep_tendsto
      latticeSpacing A.latticeSpacing_pos A.latticeSpacing_tendsto_zero t
  have harg :
      Tendsto
        (fun n =>
          -A.massRate n *
            ((physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n))
        atTop
        (nhds (-A.mass * (t : ℝ))) :=
    A.derivedMassRate_tendsto.neg.mul htime
  simpa only [floorFactor] using harg.rexp

/-- Equivalent geometric-power form of the same derived-rate continuum limit. -/
theorem floorPow_tendsto
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) :
    Tendsto
      (fun n =>
        (transferFactor n) ^
          physicalTemporalFloorNatStep latticeSpacing t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  have h := A.floorFactor_tendsto t
  convert h using 1
  funext n
  exact (A.floorFactor_eq_pow t n).symm

/-- Half-time norm-square factor used by OS quadratic estimates. -/
def floorHalfQuadraticFactor
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) (n : ℕ) : ℝ :=
  (A.floorFactor (t / 2) n) ^ 2

/-- The realizable half-time squared factor converges to the full-time
continuum quadratic factor with the mass obtained from the discrete transfer
rate limit. -/
theorem floorHalfQuadraticFactor_tendsto
    (A : PositiveDiscreteTransferRateLimit latticeSpacing transferFactor)
    (t : NNReal) :
    Tendsto
      (fun n => A.floorHalfQuadraticFactor t n)
      atTop
      (nhds (Real.exp (-A.mass * (t : ℝ)))) := by
  have h := A.floorFactor_tendsto (t / 2)
  have hsq := h.mul h
  convert hsq using 1
  · funext n
    simp only [floorHalfQuadraticFactor, pow_two]
  · rw [← Real.exp_add]
    congr 1
    norm_num [NNReal.coe_div]
    ring

end PositiveDiscreteTransferRateLimit

end

end MathlibAnalytic
end MGAP4D
