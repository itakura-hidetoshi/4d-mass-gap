import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteLocality
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The energy observable associated with one oriented plaquette. -/
def FiniteOrientedLatticeWilsonSystem.plaquetteObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette) : L.Configuration → ℝ :=
  fun A => L.plaquetteEnergy (L.plaquetteHolonomy A p)

/-- A unit upper bound for the plaquette energy. Together with the nonnegativity
already carried by the Wilson system, this places every plaquette observable in
`[0,1]`. -/
structure FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound
    (L : FiniteOrientedLatticeWilsonSystem) : Prop where
  le_one : ∀ g : L.Gauge, L.plaquetteEnergy g ≤ 1

/-- Changing one physical link outside a plaquette boundary leaves that
plaquette observable unchanged. -/
theorem finite_oriented_plaquetteObservable_eq_of_agreeOffLink_of_not_touches
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (A B : L.Configuration)
    (source : L.Edge)
    (hAgree : L.AgreeOffLink A B source)
    (hNotTouch : ¬ L.PlaquetteTouchesEdge p source) :
    L.plaquetteObservable p A = L.plaquetteObservable p B := by
  unfold FiniteOrientedLatticeWilsonSystem.plaquetteObservable
  congr 1
  apply finite_oriented_plaquetteHolonomy_congr
  intro k
  apply hAgree
  intro hBoundary
  exact hNotTouch ⟨k, hBoundary⟩

/-- Under a unit plaquette-energy bound, the values of one plaquette observable
differ by at most one between arbitrary configurations. -/
theorem finite_oriented_abs_plaquetteObservable_sub_le_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (U : FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound L)
    (p : L.Plaquette)
    (A B : L.Configuration) :
    |L.plaquetteObservable p A - L.plaquetteObservable p B| ≤ 1 := by
  have hA0 : 0 ≤ L.plaquetteObservable p A :=
    L.plaquetteEnergy_nonneg _
  have hA1 : L.plaquetteObservable p A ≤ 1 :=
    U.le_one _
  have hB0 : 0 ≤ L.plaquetteObservable p B :=
    L.plaquetteEnergy_nonneg _
  have hB1 : L.plaquetteObservable p B ≤ 1 :=
    U.le_one _
  rw [abs_le]
  constructor <;> linarith

/-- The exact support indicator for the link variation of one plaquette
observable. It is one on the four physical boundary links and zero elsewhere. -/
def FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (source : L.Edge) : ℝ := by
  classical
  exact if L.PlaquetteTouchesEdge p source then 1 else 0

/-- The plaquette-observable link-variation profile is nonnegative. -/
theorem finite_oriented_plaquetteObservableLinkVariation_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (p : L.Plaquette)
    (source : L.Edge) :
    0 ≤ L.plaquetteObservableLinkVariation p source := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation
  split_ifs <;> norm_num

/-- The support indicator gives a proof-relevant one-link oscillation bound for
one plaquette observable. Outside the four-link boundary the oscillation is
exactly zero; on the boundary it is at most one. -/
theorem finite_oriented_plaquetteObservable_variation_bound
    (L : FiniteOrientedLatticeWilsonSystem)
    (U : FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound L)
    (p : L.Plaquette)
    (source : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B source) :
    |L.plaquetteObservable p A - L.plaquetteObservable p B| ≤
      L.plaquetteObservableLinkVariation p source := by
  classical
  by_cases hTouch : L.PlaquetteTouchesEdge p source
  · simpa [FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation,
      hTouch] using
      finite_oriented_abs_plaquetteObservable_sub_le_one L U p A B
  · have hEq :=
      finite_oriented_plaquetteObservable_eq_of_agreeOffLink_of_not_touches
        L p A B source hAgree hTouch
    simp [FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation,
      hTouch, hEq]

/-- The concrete periodic `Z₂` plaquette energy is bounded above by one. -/
def z2PeriodicHypercubicOrientedPlaquetteEnergyUnitBound
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) :=
  { le_one := by
      classical
      intro g
      change (if g = 1 then 0 else 1) ≤ (1 : ℝ)
      split_ifs <;> norm_num }

/-- Concrete periodic plaquette-observable link variation. -/
def periodicHypercubicPlaquetteObservableLinkVariation
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (source : PeriodicHypercubicEdge n) : ℝ := by
  classical
  exact if periodicHypercubicPlaquetteTouchesEdge n p source then 1 else 0

/-- The concrete variation is supported exactly on the physical four-link
plaquette boundary. -/
@[simp] theorem periodicHypercubicPlaquetteObservableLinkVariation_eq
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (source : PeriodicHypercubicEdge n) :
    periodicHypercubicPlaquetteObservableLinkVariation n p source =
      if source ∈ periodicHypercubicPlaquetteEdges n p then 1 else 0 := by
  classical
  simp [periodicHypercubicPlaquetteObservableLinkVariation,
    periodicHypercubic_mem_plaquetteEdges_iff]

/-- For the periodic `Z₂` Wilson system, the selected plaquette observable has
link variation one on its boundary and zero off its boundary. -/
theorem z2PeriodicHypercubicOriented_plaquetteObservable_variation_bound
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (source : PeriodicHypercubicEdge n)
    (A B :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration)
    (hAgree :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).AgreeOffLink
        A B source) :
    |(z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).plaquetteObservable p A -
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).plaquetteObservable p B| ≤
      periodicHypercubicPlaquetteObservableLinkVariation n p source := by
  classical
  simpa [FiniteOrientedLatticeWilsonSystem.plaquetteObservableLinkVariation,
    periodicHypercubicPlaquetteObservableLinkVariation,
    z2PeriodicHypercubicOrientedWilsonSystem_touches_iff] using
    finite_oriented_plaquetteObservable_variation_bound
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      (z2PeriodicHypercubicOrientedPlaquetteEnergyUnitBound n beta hBeta)
      p source A B hAgree

end

end MathlibAnalytic
end MGAP4D
