import MGAP4D.MathlibAnalytic.UniformQuadraticCoercivityLimitPosDef
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingContinuumSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumVacuum
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCommonProductFiniteOSGramPosDefPhysicalCarrier

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The remaining strict-OS kinematic datum expressed as volume-uniform
coercivity on every finite family of common positive-time observables.

For a finite index set `s`, the constant `δ` may depend on `s`, but it is
uniform in the Wilson volume index `n`.  This is exactly the strength needed
for strict positivity to survive the weak-star continuum limit. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra
  uniformFiniteOSCoercivity : ∀ s : Finset ℕ,
    ∃ δ : ℝ, 0 < δ ∧ ∀ n (x : s → ℝ),
      δ * (∑ i, x i ^ 2) ≤
        D.osBilinForm
          (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
          (∑ i : s, x i •
            physicalYangMillsPositiveTimeToSubmodule D
              (observable (i : ℕ)))
          (∑ i : s, x i •
            physicalYangMillsPositiveTimeToSubmodule D
              (observable (i : ℕ)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
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

/-- Volume-uniform finite Wilson OS coercivity passes to strict positive
definiteness of the corresponding continuum OS Gram matrix.  The proof uses
only convergence of the diagonal quadratic value of each fixed finite linear
combination, not entrywise matrix convergence. -/
theorem continuum_osGram_posDef
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData
      S D halfExtent N hN beta hbeta B hInvariant)
    (s : Finset ℕ) :
    Matrix.PosDef
      ((fun i j : s =>
        D.osBilinForm
          (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
          (physicalYangMillsPositiveTimeToSubmodule D
            (J.observable (i : ℕ)))
          (physicalYangMillsPositiveTimeToSubmodule D
            (J.observable (j : ℕ)))) : Matrix s s ℝ) := by
  classical
  letI : AddCommGroup D.positiveTimeSubalgebra.toSubmodule :=
    Submodule.addCommGroup (p := D.positiveTimeSubalgebra.toSubmodule)
  letI : Module ℝ D.positiveTimeSubalgebra.toSubmodule :=
    Submodule.module (p := D.positiveTimeSubalgebra.toSubmodule)
  let w : s → D.positiveTimeSubalgebra.toSubmodule := fun i =>
    physicalYangMillsPositiveTimeToSubmodule D (J.observable (i : ℕ))
  let A : ℕ → Matrix s s ℝ := fun n i j =>
    D.osBilinForm
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)
      (w i) (w j)
  let A_limit : Matrix s s ℝ := fun i j =>
    D.osBilinForm
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
      (w i) (w j)
  rcases J.uniformFiniteOSCoercivity s with ⟨δ, hδ, hcoercive⟩
  have hSymm :
      (D.osBilinForm
        (physicalYangMillsContinuumGaugeInvariantWeakStarState S)).IsSymm :=
    D.osBilinForm_isSymm
      (physicalYangMillsContinuumGaugeInvariantWeakStarState S)
      (physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
        S D hInvariant)
  have hHermitian : A_limit.IsHermitian := by
    exact bilinForm_matrix_isHermitian_of_isSymm
      (D.osBilinForm
        (physicalYangMillsContinuumGaugeInvariantWeakStarState S))
      hSymm w
  have hTendsto : ∀ x : s → ℝ,
      Filter.Tendsto
        (fun n : ℕ => star x ⬝ᵥ (A n *ᵥ x))
        Filter.atTop
        (nhds (star x ⬝ᵥ (A_limit *ᵥ x))) := by
    intro x
    have h :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_osBilinForm_tendsto
        S D
        (∑ i : s, x i • w i)
        (∑ i : s, x i • w i)
    simpa [A, A_limit, bilinForm_matrix_quadratic_eq] using h
  have hCoercive : ∀ n (x : s → ℝ),
      δ * (∑ i, x i ^ 2) ≤ star x ⬝ᵥ (A n *ᵥ x) := by
    intro n x
    simpa [A, w, bilinForm_matrix_quadratic_eq] using hcoercive n x
  have hPosDef :=
    matrix_posDef_of_uniform_quadratic_coercivity_tendsto
      A A_limit hHermitian δ hδ hTendsto hCoercive
  simpa [A_limit, w] using hPosDef

/-- The continuum pre-Hilbert carrier form of the same result, written exactly
in the interface expected by the finite-Gram package integrated in #1602. -/
theorem continuum_carrier_osGram_posDef
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData
      S D halfExtent N hN beta hbeta B hInvariant)
    (s : Finset ℕ) :
    let P :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant
    Matrix.PosDef
      ((fun i j : s =>
        D.osBilinForm P.omega
          (P.toPositiveTime
            (P.carrierOfPositiveTime (J.observable (i : ℕ))))
          (P.toPositiveTime
            (P.carrierOfPositiveTime (J.observable (j : ℕ))))) : Matrix s s ℝ) := by
  let P :=
    physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant
  have h := J.continuum_osGram_posDef s
  simpa [P, physicalYangMillsPositiveTimeToSubmodule,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.carrierOfPositiveTime,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.toPositiveTime] using h

/-- Uniform finite-volume OS coercivity theorem-generates the finite positive
definite continuum Gram datum of #1602, and therefore all downstream
kinematic common-product carrier constructions already attached to it. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (J : PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta B hInvariant) where
  observable := fun n =>
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant).carrierOfPositiveTime
        (J.observable n)
  osGram_posDef := J.continuum_carrier_osGram_posDef

end PhysicalYangMillsEvenPeriodicWilsonOSCommonProductUniformFiniteOSCoercivityPhysicalCarrierData

end

end MathlibAnalytic
end MGAP4D
