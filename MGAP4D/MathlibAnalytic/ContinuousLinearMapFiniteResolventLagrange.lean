import Mathlib.LinearAlgebra.Lagrange
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteResolventDividedDifference
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousLinearMap

variable {ι E : Type*}
variable [DecidableEq ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The barycentric Lagrange weight at one node of a finite real node family. -/
def finiteLagrangeWeight
    (s : Finset ι)
    (parameter : ι → ℝ)
    (i : ι) : ℝ :=
  (∏ j ∈ s.erase i, (parameter i - parameter j))⁻¹

/-- The closed finite Lagrange combination of bounded operator values. -/
def finiteLagrangeCombination
    (s : Finset ι)
    (parameter : ι → ℝ)
    (A : ι → E →L[ℝ] E) :
    E →L[ℝ] E :=
  ∑ i ∈ s, finiteLagrangeWeight s parameter i • A i

@[simp] theorem finiteLagrangeCombination_apply
    (s : Finset ι)
    (parameter : ι → ℝ)
    (A : ι → E →L[ℝ] E)
    (x : E) :
    finiteLagrangeCombination s parameter A x =
      ∑ i ∈ s, finiteLagrangeWeight s parameter i • A i x := by
  simp [finiteLagrangeCombination]

@[simp] theorem finiteLagrangeCombination_empty
    (parameter : ι → ℝ)
    (A : ι → E →L[ℝ] E) :
    finiteLagrangeCombination ∅ parameter A = 0 := by
  simp [finiteLagrangeCombination]

@[simp] theorem finiteLagrangeWeight_singleton
    (parameter : ι → ℝ)
    (i : ι) :
    finiteLagrangeWeight {i} parameter i = 1 := by
  simp [finiteLagrangeWeight]

@[simp] theorem finiteLagrangeCombination_singleton
    (parameter : ι → ℝ)
    (A : ι → E →L[ℝ] E)
    (i : ι) :
    finiteLagrangeCombination {i} parameter A = A i := by
  simp [finiteLagrangeCombination]

/-- The resolvent Lagrange weight is exactly the leading coefficient of the
corresponding mathlib Lagrange basis polynomial. -/
theorem finiteLagrangeWeight_eq_lagrangeBasis_leadingCoeff
    (s : Finset ι)
    (parameter : ι → ℝ)
    (hInjective : Set.InjOn parameter (s : Set ι))
    {i : ι}
    (hi : i ∈ s) :
    finiteLagrangeWeight s parameter i =
      (Lagrange.basis s parameter i).leadingCoeff := by
  symm
  exact Lagrange.leadingCoeff_basis hInjective hi

/-- Under distinct nodes, every finite Lagrange weight is nonzero. -/
theorem finiteLagrangeWeight_ne_zero
    (s : Finset ι)
    (parameter : ι → ℝ)
    (hInjective : Set.InjOn parameter (s : Set ι))
    {i : ι}
    (hi : i ∈ s) :
    finiteLagrangeWeight s parameter i ≠ 0 := by
  unfold finiteLagrangeWeight
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro hijParameter
  have hij : i = j :=
    hInjective hi (Finset.mem_of_mem_erase hj) hijParameter
  exact (Finset.ne_of_mem_erase hj) hij.symm

/-- Pointwise convergence of a finite operator family passes to its fixed
Lagrange linear combination. -/
theorem tendsto_finiteLagrangeCombination_apply
    {κ : Type*}
    (l : Filter κ)
    (s : Finset ι)
    (parameter : ι → ℝ)
    (A : κ → ι → E →L[ℝ] E)
    (R : ι → E →L[ℝ] E)
    (hPoint : ∀ i x, Filter.Tendsto (fun k => A k i x) l (nhds (R i x)))
    (x : E) :
    Filter.Tendsto
      (fun k => finiteLagrangeCombination s parameter (A k) x)
      l
      (nhds (finiteLagrangeCombination s parameter R x)) := by
  classical
  have hWeightedSum : ∀ (t : Finset ι) (c : ι → ℝ),
      Filter.Tendsto
        (fun k => ∑ i ∈ t, c i • A k i x)
        l
        (nhds (∑ i ∈ t, c i • R i x)) := by
    intro t c
    induction t using Finset.induction_on with
    | empty =>
        simpa using
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : κ => (0 : E)) l (nhds 0))
    | @insert i t hi ih =>
        have hTerm := (hPoint i x).const_smul (c i)
        simpa [Finset.sum_insert, hi] using hTerm.add ih
  simpa [finiteLagrangeCombination] using
    hWeightedSum s (fun i => finiteLagrangeWeight s parameter i)

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
