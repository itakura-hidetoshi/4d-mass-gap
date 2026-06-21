import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A purely spatial plaquette has exactly the reflected plaquette holonomy
when evaluated in the reflected configuration. -/
theorem periodicHypercubicEvenPlaquetteHolonomy_configurationReflection_of_not_hasTimeDirection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hspace : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationReflection H A) p =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenPlaquetteReflection H p) := by
  rcases p with ⟨base, ⟨⟨mu, nu⟩, hmunu⟩⟩
  have hmu : mu ≠ 0 := by
    intro h
    apply hspace
    exact Or.inl h
  have hnu : nu ≠ 0 := by
    intro h
    apply hspace
    exact Or.inr h
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenConfigurationReflection,
    periodicHypercubicEvenEdgeReflection,
    periodicHypercubicEvenPlaquetteReflection,
    periodicHypercubicEvenReflectedPlaquetteBase,
    periodicHypercubicEvenPlaquetteHasTimeDirection,
    hmu, hnu,
    periodicHypercubicEvenTimeReflection_shift_spatial]

/-- A time-space plaquette is orientation-reversing under site reflection.
Its reflected-configuration holonomy is the inverse reflected plaquette
holonomy, conjugated to the original plaquette base point. -/
theorem periodicHypercubicEvenPlaquetteHolonomy_configurationReflection_of_hasTimeDirection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationReflection H A) p =
      (A ((periodicHypercubicEvenPlaquetteReflection H p).1, 0))⁻¹ *
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPlaquetteReflection H p))⁻¹ *
        A ((periodicHypercubicEvenPlaquetteReflection H p).1, 0) := by
  rcases p with ⟨base, ⟨⟨mu, nu⟩, hmunu⟩⟩
  have hmu : mu = 0 := by
    rcases htime with hmu | hnu
    · exact hmu
    · subst nu
      exact False.elim ((Fin.not_lt_zero mu) hmunu)
  subst mu
  have hnu : nu ≠ 0 := by
    intro h
    subst nu
    exact (lt_irrefl (0 : PeriodicHypercubicAxis)) hmunu
  simp [periodicHypercubicPlaquetteHolonomy,
    periodicHypercubicStepValue,
    periodicHypercubicBoundaryStep,
    periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis,
    periodicHypercubicEvenConfigurationReflection,
    periodicHypercubicEvenEdgeReflection,
    periodicHypercubicEvenPlaquetteReflection,
    periodicHypercubicEvenReflectedPlaquetteBase,
    periodicHypercubicEvenPlaquetteHasTimeDirection,
    hnu,
    periodicHypercubicEvenTimeReflection_shift_time,
    periodicHypercubicEvenTimeReflection_shift_spatial,
    periodicHypercubicEven_shift_unshift_time_comm,
    periodicHypercubicShift_unshift,
    periodicHypercubicUnshift_shift,
    periodicHypercubicShift_comm]
  group

end

end MathlibAnalytic
end MGAP4D
