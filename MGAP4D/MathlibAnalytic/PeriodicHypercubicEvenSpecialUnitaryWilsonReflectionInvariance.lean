import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConfigurationHaarReflectionInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion

/-!
# Reflection invariance of the actual even-periodic `SU(N)` Wilson Gibbs law

Physical Euclidean time reflection acts differently on the two classes of
coordinate plaquettes.  Purely spatial plaquettes preserve their oriented
holonomy.  A time--space plaquette reverses orientation; after the canonical
positive-link base correction its reflected holonomy is a conjugate of the
inverse of the original holonomy.

The canonical Wilson plaquette energy is invariant under both conjugation and
inversion.  Therefore the finite Wilson action is reflection invariant.  Together
with the already merged product-Haar reflection theorem, the standard tilted-
measure invariance lemma gives exact reflection invariance of the finite Gibbs
probability law.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open MeasureTheory

noncomputable section

local instance wilsonReflectionIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonReflectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonReflectionSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonReflectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonReflectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Orientation-corrected reflection as a finite plaquette equivalence. -/
def periodicHypercubicEvenPlaquetteReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenPlaquette H ≃ PeriodicHypercubicEvenPlaquette H where
  toFun := periodicHypercubicEvenPlaquetteReflection H
  invFun := periodicHypercubicEvenPlaquetteReflection H
  left_inv := periodicHypercubicEvenPlaquetteReflection_involutive H
  right_inv := periodicHypercubicEvenPlaquetteReflection_involutive H

/-- In the ordered coordinate-plane convention, a plaquette contains time iff
its first axis is time. -/
theorem periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_eq_zero
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPlaquetteHasTimeDirection p ↔
      periodicHypercubicPlaquetteFirstAxis p = 0 := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · have hlt := p.2.2
      change periodicHypercubicPlaquetteFirstAxis p <
        periodicHypercubicPlaquetteSecondAxis p at hlt
      rw [h] at hlt
      exact (Fin.not_lt_zero _ hlt).elim
  · intro h
    exact Or.inl h

/-- Reflection preserves the holonomy of a purely spatial coordinate plaquette. -/
theorem periodicHypercubicPlaquetteHolonomy_configurationReflection_spatial
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hspace : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationReflection H A)
        (periodicHypercubicEvenPlaquetteReflection H p) =
      periodicHypercubicPlaquetteHolonomy A p := by
  rcases p with ⟨v, ⟨⟨mu, nu⟩, hmunu⟩⟩
  have hmu : mu ≠ 0 := by
    intro h
    apply hspace
    exact Or.inl h
  have hnu : nu ≠ 0 := by
    intro h
    apply hspace
    exact Or.inr h
  unfold periodicHypercubicPlaquetteHolonomy
  simp [periodicHypercubicEvenPlaquetteReflection,
    periodicHypercubicEvenReflectedPlaquetteBase,
    periodicHypercubicEvenPlaquetteHasTimeDirection,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    hmu, hnu,
    periodicHypercubicEvenConfigurationReflection,
    periodicHypercubicEvenEdgeReflection_spatial,
    periodicHypercubicEvenTimeReflection_shift_spatial,
    periodicHypercubicEvenTimeReflection_involutive]

/-- Reflection of a time--space plaquette gives a conjugate of the inverse
holonomy.  The conjugating element is the original positive time link at the
plaquette base. -/
theorem periodicHypercubicPlaquetteHolonomy_configurationReflection_time
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationReflection H A)
        (periodicHypercubicEvenPlaquetteReflection H p) =
      (A (p.1, 0))⁻¹ *
        (periodicHypercubicPlaquetteHolonomy A p)⁻¹ *
        A (p.1, 0) := by
  rcases p with ⟨v, ⟨⟨mu, nu⟩, hmunu⟩⟩
  have hmu : mu = 0 :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_eq_zero
      (H := H) (v, ⟨⟨mu, nu⟩, hmunu⟩)).1 htime
  subst mu
  have hnu : nu ≠ 0 := by
    intro h
    subst nu
    exact (lt_irrefl (0 : PeriodicHypercubicAxis)) hmunu
  unfold periodicHypercubicPlaquetteHolonomy
  simp [periodicHypercubicEvenPlaquetteReflection,
    periodicHypercubicEvenReflectedPlaquetteBase,
    periodicHypercubicEvenPlaquetteHasTimeDirection,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    hnu,
    periodicHypercubicEvenConfigurationReflection,
    periodicHypercubicEvenEdgeReflection_spatial,
    periodicHypercubicEvenTimeReflection_shift_spatial,
    periodicHypercubicEvenTimeReflection_shift_time,
    periodicHypercubicEvenTimeReflection_unshift_time,
    periodicHypercubicShift_unshift,
    periodicHypercubicUnshift_shift,
    periodicHypercubicShift_comm]
  group

/-- Plaquette energy is exactly preserved by physical reflection. -/
theorem periodicHypercubicSpecialUnitaryWilsonPlaquetteEnergy_configurationReflection
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationReflection H A)
        (periodicHypercubicEvenPlaquetteReflection H p)) =
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p) := by
  by_cases htime : periodicHypercubicEvenPlaquetteHasTimeDirection p
  · rw [periodicHypercubicPlaquetteHolonomy_configurationReflection_time
      A p htime]
    calc
      specialUnitaryWilsonPlaquetteEnergy N
          ((A (p.1, 0))⁻¹ *
            (periodicHypercubicPlaquetteHolonomy A p)⁻¹ *
            A (p.1, 0)) =
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p)⁻¹ := by
            simpa using
              specialUnitaryWilsonPlaquetteEnergy_conjInvariant
                ((A (p.1, 0))⁻¹)
                ((periodicHypercubicPlaquetteHolonomy A p)⁻¹)
      _ = specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A p) :=
        specialUnitaryWilsonPlaquetteEnergy_inv
          (periodicHypercubicPlaquetteHolonomy A p)
  · rw [periodicHypercubicPlaquetteHolonomy_configurationReflection_spatial
      A p htime]

/-- The canonical finite even-periodic `SU(N)` Wilson action is invariant under
physical Euclidean time reflection. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.wilsonAction
      (periodicHypercubicEvenConfigurationReflection H A) =
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.wilsonAction A := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction,
    periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction]
  refine Fintype.sum_equiv
    (periodicHypercubicEvenPlaquetteReflectionEquiv H).symm _ _ ?_
  intro p
  simpa using
    periodicHypercubicSpecialUnitaryWilsonPlaquetteEnergy_configurationReflection
      H N A ((periodicHypercubicEvenPlaquetteReflectionEquiv H).symm p)

/-- The finite even-periodic `SU(N)` Wilson Gibbs probability law is exactly
measure-preserving under physical Euclidean time reflection. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbs_measurePreserving_reflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · exact
      periodicHypercubicEvenSpecialUnitary_configurationHaar_measurePreserving_reflection
        H N hN beta beta_nonneg
  · exact
      (continuous_compact_oriented_gibbsExponent
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg)).measurable
  · intro A
    unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    exact congrArg
      (fun x : ℝ =>
        -(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.beta * x)
      (periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection
        H N hN beta beta_nonneg A)
  · exact
      continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg)

/-- Pushforward form of finite-volume Wilson Gibbs reflection invariance. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbs_map_reflection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    Measure.map
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure :=
  (periodicHypercubicEvenSpecialUnitary_gibbs_measurePreserving_reflection
    H N hN beta beta_nonneg).map_eq

end
end MathlibAnalytic
end MGAP4D
