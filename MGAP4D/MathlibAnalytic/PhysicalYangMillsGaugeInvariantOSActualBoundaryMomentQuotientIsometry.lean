import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentLinearIsometry
import Mathlib.Analysis.Normed.Group.SeparationQuotient

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

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

/-- The already-existing coherent carrier-level boundary-moment linear map
kills every Osterwalder--Schrader seminorm-zero vector.

No new norm estimate is needed: the carrier-level `linearIsometry` already
identifies its norm with the OS seminorm. -/
theorem linearMap_eq_zero_of_norm_eq_zero
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : ‖F‖ = 0) :
    L.linearMap n F = 0 := by
  apply norm_eq_zero.mp
  calc
    ‖L.linearMap n F‖ = ‖F‖ := by
      simpa using (L.linearIsometry n).norm_map F
    _ = 0 := hF

/-- Inseparable OS carrier representatives have the same actual Wilson
boundary-moment vector. -/
theorem linearMap_eq_of_inseparable
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    ∀ F G,
      Inseparable F G → L.linearMap n F = L.linearMap n G :=
  SeparationQuotient.apply_eq_apply_of_inseparable
    (L.linearMap n)
    (fun F hF => L.linearMap_eq_zero_of_norm_eq_zero n F hF)

/-- The existing actual Wilson boundary-moment linear map descends canonically
to the separated OS null quotient. -/
noncomputable def separatedBoundaryMomentLinearMap
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toFun :=
    SeparationQuotient.lift
      (L.linearMap n)
      (L.linearMap_eq_of_inseparable n)
  map_add' := by
    intro x y
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    rcases SeparationQuotient.surjective_mk y with ⟨G, rfl⟩
    change L.linearMap n (F + G) = L.linearMap n F + L.linearMap n G
    exact (L.linearMap n).map_add F G
  map_smul' := by
    intro r x
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    change L.linearMap n (r • F) = r • L.linearMap n F
    exact (L.linearMap n).map_smul r F

@[simp] theorem separatedBoundaryMomentLinearMap_mk
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.separatedBoundaryMomentLinearMap n (SeparationQuotient.mk F) =
      L.linearMap n F :=
  rfl

/-- The descended boundary representation preserves the separated OS norm
exactly. -/
theorem separatedBoundaryMomentLinearMap_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated) :
    ‖L.separatedBoundaryMomentLinearMap n x‖ = ‖x‖ := by
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  rw [L.separatedBoundaryMomentLinearMap_mk]
  calc
    ‖L.linearMap n F‖ = ‖F‖ := by
      simpa using (L.linearIsometry n).norm_map F
    _ = ‖SeparationQuotient.mk F‖ := by
      rw [SeparationQuotient.norm_mk]

/-- Hence the separated actual finite Wilson OS space embeds real-linearly and
isometrically into the shared-boundary Haar `L²` space. -/
noncomputable def separatedBoundaryMomentLinearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toLinearMap := L.separatedBoundaryMomentLinearMap n
  norm_map' := L.separatedBoundaryMomentLinearMap_norm n

@[simp] theorem separatedBoundaryMomentLinearIsometry_mk
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.separatedBoundaryMomentLinearIsometry n (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  change
    L.separatedBoundaryMomentLinearMap n (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F
  rw [L.separatedBoundaryMomentLinearMap_mk]
  exact L.linearMap_apply n F

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end

end MathlibAnalytic
end MGAP4D
