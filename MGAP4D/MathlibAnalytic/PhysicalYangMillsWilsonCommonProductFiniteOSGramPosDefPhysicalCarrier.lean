import MGAP4D.MathlibAnalytic.FiniteGramPosDefLinearIndependent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductSeparatedLinearIndependentPhysicalCarrier

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The remaining common-product kinematic carrier expressed entirely through
finite reflected Euclidean correlation matrices.

The model supplies a countable positive-time gauge-invariant observable family.
For every finite subfamily, its actual Osterwalder--Schrader Gram matrix is
positive definite.  Mathlib then gives linear independence of every finite
quotient family and hence global linear independence of the separated OS
classes. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (P : D.OSPreHilbertData)
    (hP : P.IsNormalized) where
  observable : ℕ → P.Carrier
  osGram_posDef : ∀ s : Finset ℕ,
    Matrix.PosDef
      ((fun i j : s =>
        D.osBilinForm P.omega
          (P.toPositiveTime (observable (i : ℕ)))
          (P.toPositiveTime (observable (j : ℕ)))) : Matrix s s ℝ)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData

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

/-- The Gram matrix of the separated OS quotient classes is exactly the matrix
of the actual reflected continuum expectations stored in `osGram_posDef`. -/
theorem osClass_finset_gram_eq_osGram
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta P hP)
    (s : Finset ℕ) :
    Matrix.gram ℝ
        ((fun n => P.osClass (J.observable n)) ∘
          (Subtype.val : s → ℕ)) =
      ((fun i j : s =>
        D.osBilinForm P.omega
          (P.toPositiveTime (J.observable (i : ℕ)))
          (P.toPositiveTime (J.observable (j : ℕ)))) : Matrix s s ℝ) := by
  ext i j
  simp [Matrix.gram,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.osClass,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.inner_eq_osBilinForm]

/-- Finite strict OS Gram positivity theorem-generates global linear
independence of the separated OS observable classes. -/
theorem osClass_linearIndependent
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    LinearIndependent ℝ (fun n => P.osClass (J.observable n)) := by
  apply linearIndependent_of_finset_gram_posDef
  intro s
  rw [J.osClass_finset_gram_eq_osGram s]
  exact J.osGram_posDef s

/-- The finite-Gram criterion generates the separated-quotient linear
independence carrier of #1601. -/
noncomputable def toSeparatedLinearIndependentPhysicalCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductSeparatedLinearIndependentPhysicalCarrierData
      halfExtent N hN beta hbeta P hP where
  observable := J.observable
  osClass_linearIndependent := J.osClass_linearIndependent

/-- Consequently the complete common-product physical carrier is generated
from finite actual OS Gram positive definiteness. -/
noncomputable def toCommonProductPhysicalCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductPhysicalCarrier
      halfExtent N hN beta hbeta P :=
  J.toSeparatedLinearIndependentPhysicalCarrierData.toCommonProductPhysicalCarrier

/-- The generated common embedding retains exact vacuum preservation. -/
@[simp] theorem toCommonProductPhysicalCarrier_commonEmbed_vacuum
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta P hP) :
    J.toCommonProductPhysicalCarrier.commonEmbed
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalCommonVacuum
          halfExtent N hN beta hbeta) =
      P.vacuum := by
  exact J.toCommonProductPhysicalCarrier.commonEmbed_vacuum

/-- Thus the full mass-free family-valued finite-to-continuum ambient carrier is
theorem-generated from finite strict OS Gram positivity together with the
already canonical-sign Wilson pullback. -/
noncomputable def toMassFreeAmbientCarrier
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData

end

end MathlibAnalytic
end MGAP4D
