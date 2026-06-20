import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureFiniteGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPartialLimit
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Pointwise convergence of a finite family of real-valued functions passes
through the finite sum. -/
theorem tendsto_fintype_sum_real
    {ι : Type}
    [Fintype ι]
    (f : ℕ → ι → ℝ)
    (g : ι → ℝ)
    (h : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    Tendsto
      (fun n => ∑ i : ι, f n i)
      atTop
      (𝓝 (∑ i : ι, g i)) := by
  classical
  have hs : ∀ s : Finset ι,
      Tendsto
        (fun n => ∑ i ∈ s, f n i)
        atTop
        (𝓝 (∑ i ∈ s, g i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (h a).add ih
  simpa using hs Finset.univ

/-- For positive matrix size and nonnegative coupling, the exact one-plaquette
Wilson relative kernel on `SU(N)` is positive semidefinite.

The proof does not postulate Peter--Weyl coefficients.  Each finite Taylor
kernel is a concrete Hilbert Gram kernel.  Its finite quadratic form is
nonnegative, the quadratic forms converge by finite summation of the pointwise
kernel limits, and the nonnegative real half-line is closed. -/
theorem specialUnitaryWilsonRelativeKernel_positiveSemidefinite
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefinite
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernel N beta) := by
  intro ι _ points coefficients
  classical
  let partialQuadratic : ℕ → ℝ := fun degree =>
    ∑ p : ι × ι,
      coefficients p.1 * coefficients p.2 *
        specialUnitaryWilsonRelativeKernelPartial N beta degree
          (points p.1) (points p.2)
  let exactQuadratic : ℝ :=
    ∑ p : ι × ι,
      coefficients p.1 * coefficients p.2 *
        specialUnitaryWilsonRelativeKernel N beta
          (points p.1) (points p.2)
  have hTerm : ∀ p : ι × ι,
      Tendsto
        (fun degree =>
          coefficients p.1 * coefficients p.2 *
            specialUnitaryWilsonRelativeKernelPartial N beta degree
              (points p.1) (points p.2))
        atTop
        (𝓝
          (coefficients p.1 * coefficients p.2 *
            specialUnitaryWilsonRelativeKernel N beta
              (points p.1) (points p.2))) := by
    intro p
    have hCoefficient :
        Tendsto
          (fun _ : ℕ => coefficients p.1 * coefficients p.2)
          atTop
          (𝓝 (coefficients p.1 * coefficients p.2)) :=
      tendsto_const_nhds
    exact hCoefficient.mul
      (specialUnitaryWilsonRelativeKernelPartial_tendsto
        N beta (points p.1) (points p.2))
  have hQuadratic :
      Tendsto partialQuadratic atTop (𝓝 exactQuadratic) := by
    exact tendsto_fintype_sum_real
      (fun degree p =>
        coefficients p.1 * coefficients p.2 *
          specialUnitaryWilsonRelativeKernelPartial N beta degree
            (points p.1) (points p.2))
      (fun p =>
        coefficients p.1 * coefficients p.2 *
          specialUnitaryWilsonRelativeKernel N beta
            (points p.1) (points p.2))
      hTerm
  have hPartialNonneg : ∀ degree, 0 ≤ partialQuadratic degree := by
    intro degree
    unfold partialQuadratic
    rw [Fintype.sum_prod_type]
    exact
      (specialUnitaryWilsonRelativeKernelPartialConcreteFeature
        N hN beta hbeta degree).positiveSemidefinite
          ι points coefficients
  have hExactNonneg : 0 ≤ exactQuadratic := by
    apply le_of_tendsto hQuadratic
    exact Filter.Eventually.of_forall hPartialNonneg
  unfold exactQuadratic at hExactNonneg
  rw [Fintype.sum_prod_type] at hExactNonneg
  exact hExactNonneg

end

end MathlibAnalytic
end MGAP4D
