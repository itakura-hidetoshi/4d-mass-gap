import MGAP4D.MathlibAnalytic.SeparationQuotientStrictGramLinearIndependent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductSeparatedLinearIndependentPhysicalCarrier
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The remaining common-product kinematic carrier reduced from an abstract
linearly independent family in the separated OS quotient to a concrete strict
positivity statement for the continuum reflected Gram form.

For every nonzero finitely supported real coefficient vector, the corresponding
finite linear combination of positive-time gauge-invariant observables is
required to have strictly positive OS quadratic form.  The generic separation
quotient theorem then proves that the OS classes are linearly independent. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  observable : ℕ → P.Carrier
  osGram_strictly_positive :
    ∀ l : ℕ →₀ ℝ, l ≠ 0 →
      0 < D.osBilinForm P.omega
        (P.toPositiveTime (Finsupp.linearCombination ℝ observable l))
        (P.toPositiveTime (Finsupp.linearCombination ℝ observable l))

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {P : D.OSPreHilbertData}
    {hP : P.IsNormalized}

/-- Strict positivity of the reflected OS Gram quadratic form proves linear
independence of the corresponding separated OS classes. -/
theorem osClass_linearIndependent
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    LinearIndependent ℝ (fun n => P.osClass (J.observable n)) := by
  have hLI :
      LinearIndependent ℝ
        (fun n => SeparationQuotient.mk (J.observable n)) := by
    apply separationQuotient_linearIndependent_of_linearCombination_inner_pos
      J.observable
    intro l hl
    rw [P.inner_eq_osBilinForm]
    exact J.osGram_strictly_positive l hl
  simpa [PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.osClass] using hLI

/-- The strict Gram datum theorem-generates exactly the independent OS quotient
carrier introduced in #1601. -/
noncomputable def toSeparatedLinearIndependentPhysicalCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP where
  observable := J.observable
  osClass_linearIndependent := J.osClass_linearIndependent

/-- Hence strict reflected Gram positivity alone generates the complete
common-product-to-continuum physical carrier. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P :=
  J.toSeparatedLinearIndependentPhysicalCarrierData.toCommonProductPhysicalCarrier

/-- The common-product vacuum is still mapped exactly to the normalized
continuum physical vacuum. -/
@[simp] theorem toCommonProductPhysicalCarrier_commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.toCommonProductPhysicalCarrier.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact J.toCommonProductPhysicalCarrier.commonEmbed_vacuum

/-- The full family-valued mass-free finite-to-continuum ambient carrier is
therefore theorem-generated from strict OS Gram positivity and the existing
canonical-sign Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData
      halfExtent N hN beta hbeta P hP)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.vacuumNormalized.toWeakStarBridge)
      (hInvariant := hInvariant) P :=
  J.toSeparatedLinearIndependentPhysicalCarrierData.toMassFreeAmbientCarrier
    Q hInvariant

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductStrictGramPhysicalCarrierData

end

end MathlibAnalytic
end MGAP4D
