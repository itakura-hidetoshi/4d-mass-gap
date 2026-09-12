import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2Transfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The first slab index in the positive reflection half-cylinder. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex
    (H : ℕ) : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) :=
  ⟨0, periodicHypercubicEvenPositiveHalfCylinderSlabCount_pos H⟩

/-- The last slab index in the positive reflection half-cylinder. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex
    (H : ℕ) : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H) :=
  ⟨H, by simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex_val
    (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H).1 = 0 :=
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex_val
    (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H).1 = H :=
  rfl

/-- As soon as there are at least two slabs, the two boundary-adjacent slab
indices are distinct.  This is the exact geometric nondegeneracy needed to
peel both endpoints in one Markov step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex_ne_last
    (H : ℕ)
    (hH : 0 < H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H ≠
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H := by
  intro h
  have hv := congrArg (fun i => i.1) h
  simp only [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex_val,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex_val] at hv
  omega

/-- The ordered pair of the two reflection-fixed outer endpoint slices of a
positive-half-cylinder spatial path. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair
    {H N : ℕ}
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H),
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))

/-- The ordered pair obtained one slab inward from the two reflection-fixed
outer endpoints.  For `H = 1` the two entries coincide, exactly reflecting the
single central spatial slice. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair
    {H N : ℕ}
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H),
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))

/-- Product of all one-slab Wilson factors strictly between the two
boundary-adjacent slabs.  It is written by erasing the first and last slab
indices, which avoids any artificial reindexing of the finite interior. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) : ℝ :=
  Finset.prod
    ((Finset.univ.erase
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H)).erase
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))
    (fun i =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i))

private theorem finset_prod_eq_two_distinct_factors_mul_remainder
    {ι M : Type*}
    [DecidableEq ι]
    [CommMonoid M]
    (s : Finset ι)
    (f : ι → M)
    (a b : ι)
    (ha : a ∈ s)
    (hb : b ∈ s)
    (hab : a ≠ b) :
    Finset.prod s f =
      f a * f b * Finset.prod ((s.erase a).erase b) f := by
  have hb' : b ∈ s.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  calc
    Finset.prod s f = f a * Finset.prod (s.erase a) f := by
      symm
      exact Finset.mul_prod_erase s f ha
    _ = f a * (f b * Finset.prod ((s.erase a).erase b) f) := by
      rw [Finset.mul_prod_erase (s.erase a) f hb']
    _ = f a * f b * Finset.prod ((s.erase a).erase b) f := by
      ac_rfl

/-- Pure finite-product Markov factorization: for a nondegenerate positive
half-cylinder, the literal path kernel is the first boundary slab factor times
the last boundary slab factor times the untouched interior product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boundarySlabs_mul_interior
    (H N : ℕ)
    (hH : 0 < H)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H)) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H)) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
          H N beta path := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
  exact
    finset_prod_eq_two_distinct_factors_mul_remainder
      (Finset.univ :
        Finset (Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
      (fun i =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H)
      (Finset.mem_univ _)
      (Finset.mem_univ _)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex_ne_last
        H hH)

/-- The new literal pair-Haar one-step kernel is exactly the product of the two
boundary-adjacent slab factors of a positive-half-cylinder path.  The second
endpoint is reversed by the already-proved symmetry of the actual one-slab
Wilson kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_outer_inner_eq_boundarySlabs
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H)) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H)) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))]

/-- Exact boundary-pair Markov factorization of the literal temporal-gauge
Wilson path kernel.  For `H > 0`, one simultaneous inward step at the two fixed
boundaries is precisely the ambient pair kernel constructed in the preceding
operator theorem, leaving only the strict interior path product. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_pairKernel_mul_interior
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
          H N beta path := by
  calc
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderFirstSlabIndex H)) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderLastSlabIndex H)) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
          H N beta path :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boundarySlabs_mul_interior
        H N hH beta path
    _ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathOuterBoundaryPair path,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathInnerBoundaryPair path) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
          H N beta path := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_outer_inner_eq_boundarySlabs
        H N hN beta hbeta path]

end

end MathlibAnalytic
end MGAP4D
