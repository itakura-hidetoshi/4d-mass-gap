import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualBoundaryMomentIsometricShadow
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDenseStateMap
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Linear coherence interface for the actual Wilson shared-boundary moment.

The current weak-star bridge identifies each OS quadratic observable with a
finite reflected Wilson observable, but it chooses the corresponding
positive-half representative separately for each observable.  The quadratic
identities alone therefore do not force those representatives, or their
boundary moments, to be compatible with addition and real scalar
multiplication.

This structure isolates exactly that missing coherence: a real-linear carrier
map whose value is the already-defined canonical boundary-moment `L²` vector.
Once this datum is supplied from a same-root Wilson pullback construction, all
quotient and isometry statements below are theorem-generated. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
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
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) where
  boundaryMomentLinearMap :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryMomentLinearMap_apply :
    ∀ F,
      boundaryMomentLinearMap F =
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F

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
    {n : ℕ}

/-- The coherent boundary-moment carrier map is norm preserving.  This is not
an additional quantitative estimate: it is exactly the norm identity proved
for the actual Wilson boundary moment, transported through the coherence
field. -/
theorem boundaryMomentLinearMap_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖Q.boundaryMomentLinearMap F‖ = ‖F‖ := by
  calc
    ‖Q.boundaryMomentLinearMap F‖ =
        ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F‖ := by
      rw [Q.boundaryMomentLinearMap_apply]
    _ = ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState F‖ := by
      symm
      exact
        physicalYangMillsEvenPeriodicWilsonOSPhysicalState_norm_eq_canonicalBoundaryMomentL2_norm
          S D halfExtent N hN beta hbeta B hInvariant n F
    _ = ‖F‖ := by
      exact
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).norm_physicalState F

/-- The coherent carrier map kills every OS seminorm-zero vector. -/
theorem boundaryMomentLinearMap_eq_zero_of_norm_eq_zero
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (hF : ‖F‖ = 0) :
    Q.boundaryMomentLinearMap F = 0 := by
  apply norm_eq_zero.mp
  rw [Q.boundaryMomentLinearMap_norm F, hF]

/-- Inseparable OS carrier vectors have the same coherent boundary moment. -/
theorem boundaryMomentLinearMap_eq_of_inseparable
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ∀ F G,
      Inseparable F G →
        Q.boundaryMomentLinearMap F = Q.boundaryMomentLinearMap G := by
  exact
    SeparationQuotient.apply_eq_apply_of_inseparable
      Q.boundaryMomentLinearMap
      (fun F hF => Q.boundaryMomentLinearMap_eq_zero_of_norm_eq_zero F hF)

/-- The coherent actual Wilson boundary moment descends canonically to the
separated OS null quotient. -/
noncomputable def separatedBoundaryMomentLinearMap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) where
  toFun :=
    SeparationQuotient.lift
      Q.boundaryMomentLinearMap
      Q.boundaryMomentLinearMap_eq_of_inseparable
  map_add' := by
    intro x y
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    rcases SeparationQuotient.surjective_mk y with ⟨G, rfl⟩
    change
      Q.boundaryMomentLinearMap (F + G) =
        Q.boundaryMomentLinearMap F + Q.boundaryMomentLinearMap G
    exact Q.boundaryMomentLinearMap.map_add F G
  map_smul' := by
    intro r x
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    change
      Q.boundaryMomentLinearMap (r • F) =
        r • Q.boundaryMomentLinearMap F
    exact Q.boundaryMomentLinearMap.map_smul r F

@[simp] theorem separatedBoundaryMomentLinearMap_mk
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.separatedBoundaryMomentLinearMap (SeparationQuotient.mk F) =
      Q.boundaryMomentLinearMap F :=
  rfl

/-- The descended map preserves the separated OS norm exactly. -/
theorem separatedBoundaryMomentLinearMap_norm
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated) :
    ‖Q.separatedBoundaryMomentLinearMap x‖ = ‖x‖ := by
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  rw [Q.separatedBoundaryMomentLinearMap_mk]
  rw [Q.boundaryMomentLinearMap_norm]
  exact SeparationQuotient.norm_mk F

/-- The separated actual finite Wilson OS space embeds isometrically and
real-linearly into the shared-boundary Haar `L²` space as soon as the
observable-level boundary moment is coherently linear. -/
noncomputable def separatedBoundaryMomentLinearIsometry
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗᵢ[ℝ]
      Lp ℝ 2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) where
  __ := Q.separatedBoundaryMomentLinearMap
  norm_map' := Q.separatedBoundaryMomentLinearMap_norm

@[simp] theorem separatedBoundaryMomentLinearIsometry_mk
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant n)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    Q.separatedBoundaryMomentLinearIsometry (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  rw [separatedBoundaryMomentLinearIsometry]
  rw [Q.separatedBoundaryMomentLinearMap_mk]
  exact Q.boundaryMomentLinearMap_apply F

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end

end MathlibAnalytic
end MGAP4D
