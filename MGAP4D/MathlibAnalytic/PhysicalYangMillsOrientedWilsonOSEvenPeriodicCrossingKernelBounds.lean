import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A finite product of concrete one-plaquette Wilson crossing kernels inherits
an explicit pointwise Boltzmann floor and the unit upper bound.

This theorem is purely model-derived: every factor is the exact `SU(N)` Wilson
relative kernel pulled back along a positive-half holonomy. -/
theorem localCrossingWilsonKernel_listProduct_mem_Icc
    {X ι : Type}
    {N : ℕ}
    (hN : 0 < N)
    {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (indices : List ι)
    (positiveHalfHolonomy :
      ι → X → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (x y : X) :
    ((indices.map fun i =>
      localCrossingWilsonKernel N beta (positiveHalfHolonomy i) x y).prod) ∈
      Set.Icc ((Real.exp (-2 * beta)) ^ indices.length) 1 := by
  induction indices with
  | nil =>
      simp
  | cons i indices ih =>
      have hi :=
        localCrossingWilsonKernel_mem_Icc hN hbeta
          (positiveHalfHolonomy i) x y
      have hfloor : 0 ≤ Real.exp (-2 * beta) :=
        Real.exp_nonneg _
      have hk :
          0 ≤ localCrossingWilsonKernel N beta
            (positiveHalfHolonomy i) x y :=
        le_trans hfloor hi.1
      have hrest :
          0 ≤ ((indices.map fun j =>
            localCrossingWilsonKernel N beta
              (positiveHalfHolonomy j) x y).prod) :=
        le_trans (pow_nonneg hfloor indices.length) ih.1
      constructor
      · change
          (Real.exp (-2 * beta)) ^ (indices.length + 1) ≤
            localCrossingWilsonKernel N beta
                (positiveHalfHolonomy i) x y *
              ((indices.map fun j =>
                localCrossingWilsonKernel N beta
                  (positiveHalfHolonomy j) x y).prod)
        rw [pow_succ]
        have hmul := mul_le_mul ih.1 hi.1 hfloor hrest
        simpa [mul_comm] using hmul
      · change
          localCrossingWilsonKernel N beta
              (positiveHalfHolonomy i) x y *
            ((indices.map fun j =>
              localCrossingWilsonKernel N beta
                (positiveHalfHolonomy j) x y).prod) ≤ 1
        calc
          localCrossingWilsonKernel N beta
                (positiveHalfHolonomy i) x y *
              ((indices.map fun j =>
                localCrossingWilsonKernel N beta
                  (positiveHalfHolonomy j) x y).prod) ≤
              1 * ((indices.map fun j =>
                localCrossingWilsonKernel N beta
                  (positiveHalfHolonomy j) x y).prod) :=
            mul_le_mul_of_nonneg_right hi.2 hrest
          _ ≤ 1 * 1 :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ = 1 := by norm_num

/-- The actual even-periodic crossing kernel therefore lies between the product
of the one-plaquette Boltzmann floors and one.

The exponent is exactly the length of the canonical list of crossing
plaquettes at scale `n`; no abstract gap or transfer-contraction assumption is
used. -/
theorem physical_yang_mills_oriented_evenPeriodic_crossingKernel_mem_Icc
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent)
    (n : ℕ)
    (x y : H.HalfConfiguration) :
    H.crossingKernel n x y ∈
      Set.Icc
        ((Real.exp (-2 * beta n)) ^
          (periodicHypercubicEvenCrossingPlaquetteList
            (halfExtent n)).length)
        1 := by
  rw [C.crossingKernel_eq_localWilsonProduct n x y]
  exact localCrossingWilsonKernel_listProduct_mem_Icc
    C.hN (C.hbeta n)
    (periodicHypercubicEvenCrossingPlaquetteList (halfExtent n))
    (C.positiveHalfHolonomy n) x y

/-- In particular, the actual even-periodic crossing kernel is strictly
positive at every pair of half-configurations. -/
theorem physical_yang_mills_oriented_evenPeriodic_crossingKernel_pos
    {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E.PhysicalGaugeAction}
    {L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E.toLatticeEmbedding}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData
      (G.toSymmetryLimit L)}
    (H : PhysicalYangMillsOrientedWilsonOSHalfLatticeDecomposition G L D)
    {N : ℕ}
    {beta : ℕ → ℝ}
    {halfExtent : ℕ → ℕ}
    (C : PhysicalYangMillsOrientedWilsonOSEvenPeriodicLocalKernelData
      H N beta halfExtent)
    (n : ℕ)
    (x y : H.HalfConfiguration) :
    0 < H.crossingKernel n x y := by
  have hbound :=
    physical_yang_mills_oriented_evenPeriodic_crossingKernel_mem_Icc
      H C n x y
  exact lt_of_lt_of_le
    (pow_pos (Real.exp_pos (-2 * beta n)) _)
    hbound.1

end

end MathlibAnalytic
end MGAP4D
