import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite Boltzmann-weighted sum with the sign convention naturally adapted
to differentiation: `exp((-E(x)) * β)`. -/
def finiteBoltzmannWeightedSum
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ)
    (β : ℝ) : ℝ :=
  ∑ x : α, Real.exp ((-energy x) * β) * weight x

/-- The derivative at zero of one finite Boltzmann factor is minus its energy. -/
theorem finiteBoltzmannFactor_hasDerivAt_zero
    (energy : ℝ) :
    HasDerivAt (fun β : ℝ => Real.exp ((-energy) * β)) (-energy) 0 := by
  have hlinear :
      HasDerivAt (fun β : ℝ => (-energy) * β) (-energy) 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul (-energy)
  simpa using hlinear.exp

/-- Exact first variation at zero of a finite Boltzmann-weighted sum. -/
theorem finiteBoltzmannWeightedSum_hasDerivAt_zero
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedSum energy weight)
      (∑ x : α, (-energy x) * weight x)
      0 := by
  simpa [finiteBoltzmannWeightedSum] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (A := fun x : α => fun β : ℝ =>
        Real.exp ((-energy x) * β) * weight x)
      (A' := fun x : α => (-energy x) * weight x)
      (fun x _hx =>
        (finiteBoltzmannFactor_hasDerivAt_zero (energy x)).mul_const (weight x)))

@[simp] theorem finiteBoltzmannWeightedSum_zero
    {α : Type*} [Fintype α]
    (energy weight : α → ℝ) :
    finiteBoltzmannWeightedSum energy weight 0 = ∑ x : α, weight x := by
  simp [finiteBoltzmannWeightedSum]

/-- A fixed scalar prefactor may be retained outside a finite Boltzmann sum.
This covers temporal-link normalization factors and geometric embedding scales. -/
def finiteBoltzmannWeightedProfile
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ)
    (β : ℝ) : ℝ :=
  scale * finiteBoltzmannWeightedSum energy weight β

/-- Exact first variation of a scalar-prefactored finite Boltzmann profile. -/
theorem finiteBoltzmannWeightedProfile_hasDerivAt_zero
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ) :
    HasDerivAt
      (finiteBoltzmannWeightedProfile scale energy weight)
      (scale * ∑ x : α, (-energy x) * weight x)
      0 := by
  exact (finiteBoltzmannWeightedSum_hasDerivAt_zero energy weight).const_mul scale

@[simp] theorem finiteBoltzmannWeightedProfile_zero
    {α : Type*} [Fintype α]
    (scale : ℝ)
    (energy weight : α → ℝ) :
    finiteBoltzmannWeightedProfile scale energy weight 0 =
      scale * ∑ x : α, weight x := by
  simp [finiteBoltzmannWeightedProfile]

/-- Projective cross-difference of four scalar profiles.  In the cross-volume
application these are the fine coefficient at `(A,b)`, coarse anchor,
fine anchor, and coarse coefficient at `(A,b)`. -/
def projectiveCrossDifference
    (fine coarseAnchor fineAnchor coarse : ℝ → ℝ)
    (β : ℝ) : ℝ :=
  fine β * coarseAnchor β - fineAnchor β * coarse β

/-- Product-rule first variation of the projective cross-difference. -/
theorem projectiveCrossDifference_hasDerivAt_zero
    (fine coarseAnchor fineAnchor coarse : ℝ → ℝ)
    (fine' coarseAnchor' fineAnchor' coarse' : ℝ)
    (hFine : HasDerivAt fine fine' 0)
    (hCoarseAnchor : HasDerivAt coarseAnchor coarseAnchor' 0)
    (hFineAnchor : HasDerivAt fineAnchor fineAnchor' 0)
    (hCoarse : HasDerivAt coarse coarse' 0) :
    HasDerivAt
      (projectiveCrossDifference fine coarseAnchor fineAnchor coarse)
      ((fine' * coarseAnchor 0 + fine 0 * coarseAnchor') -
        (fineAnchor' * coarse 0 + fineAnchor 0 * coarse'))
      0 := by
  exact (hFine.mul hCoarseAnchor).sub (hFineAnchor.mul hCoarse)

/-- If all four profiles are finite Boltzmann profiles, their projective
cross-difference has an explicit finite energy-moment first variation. -/
theorem finiteBoltzmannProjectiveCrossDifference_hasDerivAt_zero
    {αFine αCoarseAnchor αFineAnchor αCoarse : Type*}
    [Fintype αFine] [Fintype αCoarseAnchor]
    [Fintype αFineAnchor] [Fintype αCoarse]
    (sFine sCoarseAnchor sFineAnchor sCoarse : ℝ)
    (eFine wFine : αFine → ℝ)
    (eCoarseAnchor wCoarseAnchor : αCoarseAnchor → ℝ)
    (eFineAnchor wFineAnchor : αFineAnchor → ℝ)
    (eCoarse wCoarse : αCoarse → ℝ) :
    HasDerivAt
      (projectiveCrossDifference
        (finiteBoltzmannWeightedProfile sFine eFine wFine)
        (finiteBoltzmannWeightedProfile sCoarseAnchor eCoarseAnchor wCoarseAnchor)
        (finiteBoltzmannWeightedProfile sFineAnchor eFineAnchor wFineAnchor)
        (finiteBoltzmannWeightedProfile sCoarse eCoarse wCoarse))
      (((sFine * ∑ x : αFine, (-eFine x) * wFine x) *
            finiteBoltzmannWeightedProfile
              sCoarseAnchor eCoarseAnchor wCoarseAnchor 0 +
          finiteBoltzmannWeightedProfile sFine eFine wFine 0 *
            (sCoarseAnchor *
              ∑ x : αCoarseAnchor, (-eCoarseAnchor x) * wCoarseAnchor x)) -
        ((sFineAnchor *
              ∑ x : αFineAnchor, (-eFineAnchor x) * wFineAnchor x) *
            finiteBoltzmannWeightedProfile sCoarse eCoarse wCoarse 0 +
          finiteBoltzmannWeightedProfile sFineAnchor eFineAnchor wFineAnchor 0 *
            (sCoarse * ∑ x : αCoarse, (-eCoarse x) * wCoarse x)))
      0 := by
  exact projectiveCrossDifference_hasDerivAt_zero
    (finiteBoltzmannWeightedProfile sFine eFine wFine)
    (finiteBoltzmannWeightedProfile sCoarseAnchor eCoarseAnchor wCoarseAnchor)
    (finiteBoltzmannWeightedProfile sFineAnchor eFineAnchor wFineAnchor)
    (finiteBoltzmannWeightedProfile sCoarse eCoarse wCoarse)
    (sFine * ∑ x : αFine, (-eFine x) * wFine x)
    (sCoarseAnchor * ∑ x : αCoarseAnchor, (-eCoarseAnchor x) * wCoarseAnchor x)
    (sFineAnchor * ∑ x : αFineAnchor, (-eFineAnchor x) * wFineAnchor x)
    (sCoarse * ∑ x : αCoarse, (-eCoarse x) * wCoarse x)
    (finiteBoltzmannWeightedProfile_hasDerivAt_zero sFine eFine wFine)
    (finiteBoltzmannWeightedProfile_hasDerivAt_zero
      sCoarseAnchor eCoarseAnchor wCoarseAnchor)
    (finiteBoltzmannWeightedProfile_hasDerivAt_zero
      sFineAnchor eFineAnchor wFineAnchor)
    (finiteBoltzmannWeightedProfile_hasDerivAt_zero sCoarse eCoarse wCoarse)

end

end MathlibAnalytic
end MGAP4D