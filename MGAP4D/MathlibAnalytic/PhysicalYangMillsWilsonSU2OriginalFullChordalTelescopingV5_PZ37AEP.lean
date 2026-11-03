import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDistanceDependentRhoPerronHarnackV5_PZ37AEO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEP — finite link telescoping for original SU(2) rho and q

AEO proved the exact finite-volume one-link original joint sqrt-density
and JQ inverse-transfer density Harnack with factor
  exp (13*beta0*d_J(g,h))
on each of the two original interacting physical boundary slices.

The present module proves a generic, fully typed finite-coordinate
telescoping lemma for a function on a finite dependent-free product,
then applies it to the TWO original boundary configurations. The true
original full metric is the calibrated all-link l1 sum
  D_H(z,w) = ∑ e, (d_J(z.left e,w.left e)+d_J(z.right e,w.right e)).

The resulting unconditional original finite-H comparisons are
  rho_H(z) <= exp(13*beta0*D_H(z,w)) * rho_H(w),
  q_H(z) <= exp(13*beta0*D_H(z,w)) * q_H(w)
for EVERY original two-boundary pair z,w, and both reverse directions.
The coefficient 13*beta0 is independent of H; D_H counts all true links.

No new Haar measure, independent posterior, physical gap, spectral
source, continuum limit or H-uniform coercivity is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The exact finite path from configuration a to configuration b,
where precisely the coordinates in s have been updated to b. -/
def p4Q2PZ37AEP_finiteBlend
    {ι G : Type*} [DecidableEq ι]
    (a b : ι → G) (s : Finset ι) : ι → G :=
  fun j => if j ∈ s then b j else a j

theorem p4Q2PZ37AEP_finiteBlend_updateOld
    {ι G : Type*} [DecidableEq ι]
    (a b : ι → G) (s : Finset ι) (i : ι)
    (hi : i ∉ s) :
    Function.update (p4Q2PZ37AEP_finiteBlend a b s) i (a i) =
      p4Q2PZ37AEP_finiteBlend a b s := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp [p4Q2PZ37AEP_finiteBlend, hi]
  · simp [p4Q2PZ37AEP_finiteBlend, hj]

theorem p4Q2PZ37AEP_finiteBlend_insert
    {ι G : Type*} [DecidableEq ι]
    (a b : ι → G) (s : Finset ι) (i : ι)
    (hi : i ∉ s) :
    Function.update (p4Q2PZ37AEP_finiteBlend a b s) i (b i) =
      p4Q2PZ37AEP_finiteBlend a b (insert i s) := by
  classical
  funext j
  by_cases hj : j = i
  · subst j
    simp [p4Q2PZ37AEP_finiteBlend]
  · simp [p4Q2PZ37AEP_finiteBlend, Finset.mem_insert, hj, Ne.symm hj]

/-- The one-link exponential Harnack inequality descends along
EVERY finite chain of genuine coordinate updates.
No positive/normalized density assumption is necessary: only
the positivity of the real exponential multipliers is used. -/
theorem p4Q2PZ37AEP_finiteCoordinateHarnack
    {ι G : Type*} [Fintype ι] [DecidableEq ι]
    (d : G → G → ℝ) (c : ℝ)
    (f : (ι → G) → ℝ)
    (hLocal : ∀ (u : ι → G) (i : ι) (g h : G),
      f (Function.update u i g) ≤
        Real.exp (c * d g h) * f (Function.update u i h))
    (a b : ι → G) :
    f a ≤ Real.exp (c * ∑ i : ι, d (a i) (b i)) * f b := by
  have hPath : ∀ s : Finset ι,
      f a ≤
        Real.exp (c * ∑ j ∈ s, d (a j) (b j)) *
          f (p4Q2PZ37AEP_finiteBlend a b s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [p4Q2PZ37AEP_finiteBlend] using (le_refl (f a))
    | @insert i s hi ih =>
        let u := p4Q2PZ37AEP_finiteBlend a b s
        have hOld : Function.update u i (a i) = u :=
          p4Q2PZ37AEP_finiteBlend_updateOld a b s i hi
        have hNew : Function.update u i (b i) =
            p4Q2PZ37AEP_finiteBlend a b (insert i s) :=
          p4Q2PZ37AEP_finiteBlend_insert a b s i hi
        have hStep :
            f u ≤ Real.exp (c * d (a i) (b i)) *
                f (p4Q2PZ37AEP_finiteBlend a b (insert i s)) := by
          have h := hLocal u i (a i) (b i)
          rw [hOld, hNew] at h
          exact h
        calc
          f a ≤
              Real.exp (c * ∑ j ∈ s, d (a j) (b j)) *
                f (p4Q2PZ37AEP_finiteBlend a b s) := ih
          _ ≤ Real.exp (c * ∑ j ∈ s, d (a j) (b j)) *
                (Real.exp (c * d (a i) (b i)) *
                  f (p4Q2PZ37AEP_finiteBlend a b (insert i s))) :=
              mul_le_mul_of_nonneg_left hStep (Real.exp_pos _).le
          _ = Real.exp (c * ∑ j ∈ insert i s, d (a j) (b j)) *
                f (p4Q2PZ37AEP_finiteBlend a b (insert i s)) := by
              rw [Finset.sum_insert hi]
              calc
                Real.exp (c * ∑ j ∈ s, d (a j) (b j)) *
                    (Real.exp (c * d (a i) (b i)) *
                      f (p4Q2PZ37AEP_finiteBlend a b (insert i s))) =
                    Real.exp ((c * ∑ j ∈ s, d (a j) (b j)) +
                      c * d (a i) (b i)) *
                      f (p4Q2PZ37AEP_finiteBlend a b (insert i s)) := by
                        rw [Real.exp_add]
                        ring
                _ = Real.exp (c * (d (a i) (b i) +
                      ∑ j ∈ s, d (a j) (b j))) *
                      f (p4Q2PZ37AEP_finiteBlend a b (insert i s)) := by
                        congr 1
                        ring
  simpa [p4Q2PZ37AEP_finiteBlend] using (hPath Finset.univ)

/-- Two genuine boundary configurations: telescope first the second
slice, then the first slice, with NO independence assumption. -/
theorem p4Q2PZ37AEP_finiteTwoBoundaryHarnack
    {ι G : Type*} [Fintype ι] [DecidableEq ι]
    (d : G → G → ℝ) (c : ℝ)
    (F : (ι → G) × (ι → G) → ℝ)
    (hLeft : ∀ (A B : ι → G) (i : ι) (g h : G),
      F (Function.update A i g, B) ≤
        Real.exp (c * d g h) * F (Function.update A i h, B))
    (hRight : ∀ (A B : ι → G) (i : ι) (g h : G),
      F (A, Function.update B i g) ≤
        Real.exp (c * d g h) * F (A, Function.update B i h))
    (A B C D : ι → G) :
    F (A, B) ≤
      Real.exp (c * ∑ i : ι, (d (A i) (C i) + d (B i) (D i))) *
        F (C, D) := by
  have hR :
      F (A, B) ≤
        Real.exp (c * ∑ i : ι, d (B i) (D i)) * F (A, D) := by
    exact p4Q2PZ37AEP_finiteCoordinateHarnack d c
      (fun v => F (A, v))
      (by
        intro u i g h
        exact hRight A u i g h)
      B D
  have hL :
      F (A, D) ≤
        Real.exp (c * ∑ i : ι, d (A i) (C i)) * F (C, D) := by
    exact p4Q2PZ37AEP_finiteCoordinateHarnack d c
      (fun u => F (u, D))
      (by
        intro v i g h
        exact hLeft v D i g h)
      A C
  calc
    F (A, B) ≤
        Real.exp (c * ∑ i : ι, d (B i) (D i)) * F (A, D) := hR
    _ ≤ Real.exp (c * ∑ i : ι, d (B i) (D i)) *
          (Real.exp (c * ∑ i : ι, d (A i) (C i)) * F (C, D)) :=
        mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    _ = Real.exp (c * ∑ i : ι, (d (A i) (C i) + d (B i) (D i))) *
          F (C, D) := by
      rw [Finset.sum_add_distrib]
      calc
        Real.exp (c * ∑ i : ι, d (B i) (D i)) *
            (Real.exp (c * ∑ i : ι, d (A i) (C i)) * F (C, D)) =
          Real.exp ((c * ∑ i : ι, d (B i) (D i)) +
            (c * ∑ i : ι, d (A i) (C i))) * F (C, D) := by
              rw [Real.exp_add]
              ring
        _ = Real.exp (c *
              ((∑ i : ι, d (A i) (C i)) +
                (∑ i : ι, d (B i) (D i)))) * F (C, D) := by
              congr 1
              ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEP_finiteBlend_updateOld
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEP_finiteBlend_insert
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEP_finiteCoordinateHarnack
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEP_finiteTwoBoundaryHarnack
