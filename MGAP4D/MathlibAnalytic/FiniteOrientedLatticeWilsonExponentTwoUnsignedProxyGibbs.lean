import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyConditional
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For exponent-two groups, proxy and native oriented global Boltzmann weights
coincide pointwise. -/
theorem finite_oriented_unsignedProxy_boltzmannWeight_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration) :
    L.unsignedProxy.boltzmannWeight A = L.boltzmannWeight A := by
  unfold FiniteLatticeWilsonSystem.boltzmannWeight
    FiniteOrientedLatticeWilsonSystem.boltzmannWeight
  change ENNReal.ofReal
      (Real.exp (-L.beta * L.unsignedProxy.wilsonAction A)) =
    ENNReal.ofReal
      (Real.exp (-L.beta * L.wilsonAction A))
  rw [finite_oriented_unsignedProxy_wilsonAction_eq L hInv]

/-- For exponent-two groups, proxy and native oriented partition functions
coincide. -/
theorem finite_oriented_unsignedProxy_partitionFunction_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g) :
    L.unsignedProxy.partitionFunction = L.partitionFunction := by
  unfold FiniteLatticeWilsonSystem.partitionFunction
    FiniteOrientedLatticeWilsonSystem.partitionFunction
  apply tsum_congr
  intro A
  exact finite_oriented_unsignedProxy_boltzmannWeight_eq L hInv A

/-- For exponent-two groups, proxy and native oriented global Gibbs PMFs
coincide. -/
theorem finite_oriented_unsignedProxy_gibbsPMF_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g) :
    L.unsignedProxy.gibbsPMF = L.gibbsPMF := by
  ext A
  change
    L.unsignedProxy.boltzmannWeight A *
        (L.unsignedProxy.partitionFunction)⁻¹ =
      L.boltzmannWeight A *
        (L.partitionFunction)⁻¹
  rw [finite_oriented_unsignedProxy_boltzmannWeight_eq L hInv A,
    finite_oriented_unsignedProxy_partitionFunction_eq L hInv]

/-- Real Gibbs probabilities agree between the proxy and native oriented
realizations. -/
theorem finite_oriented_unsignedProxy_gibbsProbabilityReal_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration) :
    L.unsignedProxy.gibbsProbabilityReal A =
      L.gibbsProbabilityReal A := by
  unfold FiniteLatticeWilsonSystem.gibbsProbabilityReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  rw [finite_oriented_unsignedProxy_gibbsPMF_eq L hInv]
  rfl

/-- Gibbs expectations agree between the proxy and native oriented
realizations. -/
theorem finite_oriented_unsignedProxy_gibbsExpectationReal_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ) :
    L.unsignedProxy.gibbsExpectationReal f =
      L.gibbsExpectationReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
    FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  apply Finset.sum_congr
  · apply Finset.ext
    intro A
    constructor
    · intro _
      exact @Finset.mem_univ _ Pi.instFintype A
    · intro _
      exact @Finset.mem_univ _ Pi.instFintype A
  · intro A _hA
    rw [finite_oriented_unsignedProxy_gibbsProbabilityReal_eq L hInv A]

/-- Gibbs variances agree between the proxy and native oriented realizations. -/
theorem finite_oriented_unsignedProxy_gibbsVarianceReal_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (f : L.Configuration → ℝ) :
    L.unsignedProxy.gibbsVarianceReal f =
      L.gibbsVarianceReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsVarianceReal
    FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
  rw [finite_oriented_unsignedProxy_gibbsExpectationReal_eq L hInv f]
  apply Finset.sum_congr
  · apply Finset.ext
    intro A
    constructor
    · intro _
      exact @Finset.mem_univ _ Pi.instFintype A
    · intro _
      exact @Finset.mem_univ _ Pi.instFintype A
  · intro A _hA
    rw [finite_oriented_unsignedProxy_gibbsProbabilityReal_eq L hInv A]

end

end MathlibAnalytic
end MGAP4D
