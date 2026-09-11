import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicCanonicalPlaquetteIncidenceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- For a fixed first axis, canonical sorting with a distinct transverse axis is
injective in that transverse axis. -/
theorem periodicHypercubicAxisPairOfNe_fixedLeft_injective
    (mu : PeriodicHypercubicAxis) :
    Function.Injective
      (fun nu : PeriodicHypercubicOtherAxis mu =>
        periodicHypercubicAxisPairOfNe mu nu.1 nu.2) := by
  intro nuA nuB h
  rcases nuA with ⟨a, ha⟩
  rcases nuB with ⟨b, hb⟩
  apply Subtype.ext
  change a = b
  fin_cases mu <;> fin_cases a <;> fin_cases b <;>
    simp_all [periodicHypercubicAxisPairOfNe]

/-- In a nondegenerate periodic box, the three-transverse-axis/two-side
parametrization of target-incident plaquettes has no duplicates. -/
theorem periodicHypercubicIncidentPlaquette_fixedTarget_injective
    (n : ℕ)
    (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n) :
    Function.Injective
      (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
        periodicHypercubicIncidentPlaquette n target data.1 data.2) := by
  rcases target with ⟨x, mu⟩
  intro dataA dataB hPlaquette
  rcases dataA with ⟨nuA, sideA⟩
  rcases dataB with ⟨nuB, sideB⟩
  have hPair := congrArg Prod.snd hPlaquette
  change
    periodicHypercubicAxisPairOfNe mu nuA.1 nuA.2 =
      periodicHypercubicAxisPairOfNe mu nuB.1 nuB.2 at hPair
  have hNu : nuA = nuB :=
    periodicHypercubicAxisPairOfNe_fixedLeft_injective mu hPair
  subst nuB
  have hBase := congrArg Prod.fst hPlaquette
  change
    (if sideA then periodicHypercubicUnshift n x nuA.1 else x) =
      (if sideB then periodicHypercubicUnshift n x nuA.1 else x) at hBase
  have hUnshift : periodicHypercubicUnshift n x nuA.1 ≠ x :=
    periodicHypercubicUnshift_ne_self n hn x nuA.1
  cases sideA <;> cases sideB
  · rfl
  · exfalso
    exact hUnshift (by simpa using hBase.symm)
  · exfalso
    exact hUnshift (by simpa using hBase)
  · rfl

/-- Reindex a sum over the six canonical target-plaquette data by the actual
finite set of all plaquettes touching the target. -/
theorem periodicHypercubic_sum_incidentPlaquette_eq_sum_touching
    {M : Type*}
    [AddCommMonoid M]
    (n : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n)
    (f : PeriodicHypercubicPlaquette n → M) :
    (∑ data : PeriodicHypercubicOtherAxis target.2 × Bool,
        f (periodicHypercubicIncidentPlaquette n target data.1 data.2)) =
      (periodicHypercubicTouchingPlaquettes n target).sum f := by
  classical
  rw [← periodicHypercubicCanonicalTargetPlaquette_image_eq_touching]
  rw [Finset.sum_image]
  intro dataA _hA dataB _hB hEq
  exact periodicHypercubicIncidentPlaquette_fixedTarget_injective
    n hn target hEq

/-- Exactly six distinct coordinate plaquettes touch every physical link in a
nondegenerate periodic four-dimensional box. -/
theorem periodicHypercubicTouchingPlaquettes_card_eq_six
    (n : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (target : PeriodicHypercubicEdge n) :
    (periodicHypercubicTouchingPlaquettes n target).card = 6 := by
  have hSum :=
    periodicHypercubic_sum_incidentPlaquette_eq_sum_touching
      (M := ℕ) n hn target (fun _ => 1)
  simpa [periodicHypercubicCanonicalTargetPlaquetteIndex_card] using hSum.symm

/-- The actual target-local Wilson action is the sum over the finite touching
plaquette set, with no multiplicity from the canonical six-slot index. -/
def periodicHypercubicSpecialUnitaryTargetLocalWilsonAction
    (n N : ℕ)
    [NeZero n]
    (A : PeriodicHypercubicEdge n → SpecialUnitaryMatrixGroup N)
    (target : PeriodicHypercubicEdge n) : ℝ :=
  (periodicHypercubicTouchingPlaquettes n target).sum fun p =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)

/-- After target insertion, the canonical six-staple observable is exactly the
actual target-local Wilson action over the duplicate-free touching finset. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF_replaceLink_eq_targetLocalWilsonAction
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (A : PeriodicHypercubicEdge n → SpecialUnitaryMatrixGroup N)
    (g : SpecialUnitaryMatrixGroup N) :
    periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
        n N hn hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.replaceLink A target g) =
      periodicHypercubicSpecialUnitaryTargetLocalWilsonAction n N
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.replaceLink A target g) target := by
  rw [periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF_replaceLink_apply]
  exact periodicHypercubic_sum_incidentPlaquette_eq_sum_touching
    n hn target
      (fun p =>
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).base.replaceLink A target g) p))

end

end MathlibAnalytic
end MGAP4D
