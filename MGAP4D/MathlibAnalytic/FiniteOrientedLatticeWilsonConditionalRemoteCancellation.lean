import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonConditionalWeightFactorization

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Partition function of the target-local conditional factors. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge,
    L.targetLocalSingleLinkBoltzmannWeight A target g

/-- The target-local conditional partition function is nonzero. -/
theorem finite_oriented_targetLocalSingleLinkPartitionFunction_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetLocalSingleLinkPartitionFunction A target ≠ 0 := by
  intro hZero
  have hAll :
      ∀ g : L.Gauge,
        L.targetLocalSingleLinkBoltzmannWeight A target g = 0 := by
    simpa
      [FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction]
      using (ENNReal.tsum_eq_zero.mp hZero)
  exact
    (ne_of_gt
      (finite_oriented_targetLocalSingleLinkBoltzmannWeight_pos
        L A target default))
      (hAll default)

/-- The target-local conditional partition function is finite. -/
theorem finite_oriented_targetLocalSingleLinkPartitionFunction_ne_top
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.targetLocalSingleLinkPartitionFunction A target ≠ ∞ := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun g _hg => by
    simp
      [FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkBoltzmannWeight]

/-- The exact conditional partition function carries the same common remote
factor as every individual conditional weight. -/
theorem finite_oriented_singleLinkPartitionFunction_eq_local_mul_remote
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkPartitionFunction A target =
      L.targetLocalSingleLinkPartitionFunction A target *
        L.targetRemoteBoltzmannFactor A target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
    FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkPartitionFunction
  rw [tsum_fintype, tsum_fintype]
  simp_rw [finite_oriented_singleLinkBoltzmannWeight_eq_local_mul_remote]
  exact (Finset.sum_mul _ _ _).symm

/-- Conditional law formed only from target-local factors. -/
def FiniteOrientedLatticeWilsonSystem.targetLocalSingleLinkConditionalPMF
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : PMF L.Gauge :=
  PMF.normalize (L.targetLocalSingleLinkBoltzmannWeight A target)
    (finite_oriented_targetLocalSingleLinkPartitionFunction_ne_zero
      L A target)
    (finite_oriented_targetLocalSingleLinkPartitionFunction_ne_top
      L A target)

/-- Pointwise formula for the target-local conditional law. -/
theorem finite_oriented_targetLocalSingleLinkConditionalPMF_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.targetLocalSingleLinkConditionalPMF A target g =
      L.targetLocalSingleLinkBoltzmannWeight A target g *
        (L.targetLocalSingleLinkPartitionFunction A target)⁻¹ := by
  rfl

end

end MathlibAnalytic
end MGAP4D
