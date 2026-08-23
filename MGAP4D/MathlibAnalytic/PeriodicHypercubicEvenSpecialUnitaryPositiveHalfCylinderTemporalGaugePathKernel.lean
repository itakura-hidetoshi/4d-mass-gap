import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A sequence of spatial configurations on all time slices of the positive
reflection half-cylinder, including both fixed endpoints.  Since the cylinder
contains `H+1` adjacent slabs, a path contains `H+2` spatial slices. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath
    (H N : ℕ) : Type :=
  Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H + 1) →
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N

/-- Left spatial boundary of one slab in a positive-half-cylinder path. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
    {H N : ℕ}
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  path i.castSucc

/-- Right spatial boundary of one slab in a positive-half-cylinder path. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
    {H N : ℕ}
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  path i.succ

/-- The temporal-gauge Wilson action of a complete positive-half-cylinder path:
the sum of the symmetric actual one-slab Wilson actions over its `H+1`
adjacent slabs.  Interior spatial actions are therefore counted twice by their
half-weights, hence once in total, while the two fixed endpoint spatial actions
carry the required half-weight. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) : ℝ :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)

/-- The literal actual Wilson path-integrand across the positive reflection
half-cylinder: the product of the `H+1` temporal-gauge one-slab kernels along
the spatial path. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) : ℝ :=
  ∏ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)

/-- Finite products of Boltzmann factors combine into the Boltzmann factor of
the summed action.  This is kept generic so the half-cylinder theorem below is
only the physical specialization. -/
private theorem finset_prod_exp_neg_mul_eq_exp_neg_mul_sum
    {ι : Type}
    (beta : ℝ)
    (s : Finset ι)
    (f : ι → ℝ) :
    (∏ i in s, Real.exp (-beta * f i)) =
      Real.exp (-beta * ∑ i in s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.exp_add]
      congr 1
      ring

/-- Exact finite-volume Boltzmann formula for the complete temporal-gauge
positive-half-cylinder path integrand.  This is the integrand that a future
temporal-gauge-fixing theorem must identify with the positive-half Wilson
amplitude coming from the OS boundary construction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path =
      Real.exp
        (-beta *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight
  simp_rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact
    finset_prod_exp_neg_mul_eq_exp_neg_mul_sum beta Finset.univ
      (fun i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
          (path i.castSucc) (path i.succ))

/-- The complete temporal-gauge half-cylinder path action is nonnegative at
positive matrix rank. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        H N path := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
  exact Finset.sum_nonneg fun i _ =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H N hN
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)

/-- The actual temporal-gauge positive-half-cylinder path integrand is strictly
positive for every spatial path. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- At nonnegative coupling the complete `H+1`-slab path integrand is bounded
above by one.  This is a pointwise finite-volume statement and introduces no
uniform-in-volume spectral claim. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path ≤ 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann]
  have haction :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_nonneg
      H N hN path
  have hnonpos :
      -beta *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) haction
  calc
    Real.exp
        (-beta *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path) ≤ Real.exp 0 := Real.exp_le_exp.mpr hnonpos
    _ = 1 := Real.exp_zero

/-- Uniform absolute bound for the actual positive-half-cylinder path
integrand. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path| ≤ 1 := by
  rw [abs_of_pos
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_pos
      H N beta path)]
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_le_one
      H N hN beta hbeta path

end

end MathlibAnalytic
end MGAP4D
