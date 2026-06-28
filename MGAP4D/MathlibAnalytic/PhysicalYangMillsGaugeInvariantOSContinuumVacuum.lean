import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Vacuum pairing recovers the original state evaluation. -/
theorem inner_vacuum_physicalState
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    inner ℝ P.vacuum (P.physicalState F) = P.omega F.toGaugeInvariant := by
  change inner ℝ
      (P.physicalState P.vacuumObservable) (P.physicalState F) =
    P.omega F.toGaugeInvariant
  rw [P.inner_physicalState_physicalState, P.inner_eq_osBilinForm,
    D.osBilinForm_apply]
  change P.omega
      (D.reflection
          (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S) *
        F.toGaugeInvariant) = P.omega F.toGaugeInvariant
  simp

/-- A normalized OS vacuum is nonzero. -/
theorem vacuum_ne_zero
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) :
    P.vacuum ≠ 0 := by
  intro hzero
  have hnorm := P.norm_vacuum hP
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- The continuum even-periodic Wilson OS state is normalized. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant).IsNormalized := by
  change physicalYangMillsContinuumGaugeInvariantWeakStarState S 1 = 1
  rw [physicalYangMillsContinuumGaugeInvariantWeakStarState_apply]
  exact physicalYangMillsContinuumGaugeInvariantExpectation_one S

/-- The continuum Wilson OS vacuum has norm one. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_vacuum_norm
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    ‖(physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant).vacuum‖ = 1 := by
  apply PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.norm_vacuum
  exact physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    S D halfExtent N hN beta hbeta B hInvariant

/-- The continuum Wilson OS vacuum is nonzero. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_vacuum_ne_zero
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant).vacuum ≠ 0 := by
  apply PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.vacuum_ne_zero
  exact physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
    S D halfExtent N hN beta hbeta B hInvariant

end

end MathlibAnalytic
end MGAP4D
