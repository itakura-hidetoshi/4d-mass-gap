import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSGeneratorEigenvectorExponentialDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGeneratorIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}

/-- Every selected finite Wilson spectral value is strictly positive. -/
theorem finiteSpectralValue_pos
    {α : Type*}
    [DecidableEq α]
    (R : GeneratorIntertwiningData A F)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (V : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      F n value nodes orderCap)
    (k : V.SpectralIndex) :
    0 < V.spectralValue k :=
  lt_of_lt_of_le exactGapValueReal_pos
    (V.spectralValue_ge_exactGap k)

/-- Generator intertwining gives an `o(t)` defect between the actual finite
Wilson OS evolution of a selected spectral vector and its scalar exponential
model. -/
theorem finiteExponentialModelDefect_tendsto_spectralVector
    {α : Type*}
    [DecidableEq α]
    (R : GeneratorIntertwiningData A F)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (V : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      F n value nodes orderCap)
    (k : V.SpectralIndex) :
    Tendsto
      (fun t : NNReal =>
        (((t : NNReal) : ℝ))⁻¹ •
          (Real.exp (-V.spectralValue k * (((t : NNReal) : ℝ))) •
              R.realization.finiteRealization n (V.spectralVector k) -
            C.finiteOperator n t
              (R.realization.finiteRealization n (V.spectralVector k))))
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  have h :=
    HasRightHamiltonianValue.exponentialModelDefect_tendsto_zero
      (R.finiteStrongSemigroup n)
      (R.finiteSpectralValue_pos n value nodes orderCap V k)
      (R.hasRightHamiltonianValue_spectralVector n value nodes orderCap V k)
  simpa [finiteStrongSemigroup] using h

/-- The actual finite Wilson orbit of every selected spectral vector has the
same local scalar exponential model at each positive time. -/
theorem finiteOrbitExponentialModelDefect_tendsto_spectralVector
    {α : Type*}
    [DecidableEq α]
    (R : GeneratorIntertwiningData A F)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (V : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      F n value nodes orderCap)
    (k : V.SpectralIndex)
    (s : NNReal) :
    Tendsto
      (fun t : NNReal =>
        (((t : NNReal) : ℝ))⁻¹ •
          (Real.exp (-V.spectralValue k * (((t : NNReal) : ℝ))) •
              C.finiteOperator n s
                (R.realization.finiteRealization n (V.spectralVector k)) -
            C.finiteOperator n t
              (C.finiteOperator n s
                (R.realization.finiteRealization n (V.spectralVector k)))))
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  have h :=
    HasRightHamiltonianValue.orbitExponentialModelDefect_tendsto_zero
      (R.finiteStrongSemigroup n)
      (R.finiteSpectralValue_pos n value nodes orderCap V k)
      (R.hasRightHamiltonianValue_spectralVector n value nodes orderCap V k)
      s
  simpa [finiteStrongSemigroup] using h

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
