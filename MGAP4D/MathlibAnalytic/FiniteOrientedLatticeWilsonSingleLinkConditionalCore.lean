import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteLocality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Exact single-link Boltzmann weight obtained by varying one physical link. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-L.beta * L.wilsonAction (L.replaceLink A target g)))

/-- Every orientation-correct single-link Boltzmann weight is positive. -/
theorem finite_oriented_singleLinkBoltzmannWeight_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    0 < L.singleLinkBoltzmannWeight A target g := by
  rw [FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight,
    ENNReal.ofReal_pos]
  exact Real.exp_pos _

/-- Exact single-link conditional partition function. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : ℝ≥0∞ :=
  ∑' g : L.Gauge, L.singleLinkBoltzmannWeight A target g

/-- The exact single-link conditional partition function is nonzero. -/
theorem finite_oriented_singleLinkPartitionFunction_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkPartitionFunction A target ≠ 0 := by
  intro hZero
  have hAll :
      ∀ g : L.Gauge, L.singleLinkBoltzmannWeight A target g = 0 := by
    simpa [FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction] using
      (ENNReal.tsum_eq_zero.mp hZero)
  exact
    (ne_of_gt
      (finite_oriented_singleLinkBoltzmannWeight_pos
        L A target default))
      (hAll default)

/-- The exact single-link conditional partition function is finite. -/
theorem finite_oriented_singleLinkPartitionFunction_ne_top
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkPartitionFunction A target ≠ ∞ := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun g _hg => by
    simp [FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight]

/-- Exact single-link conditional law of the orientation-correct Wilson action. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalPMF
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge) : PMF L.Gauge :=
  PMF.normalize (L.singleLinkBoltzmannWeight A target)
    (finite_oriented_singleLinkPartitionFunction_ne_zero L A target)
    (finite_oriented_singleLinkPartitionFunction_ne_top L A target)

/-- Pointwise formula for the exact single-link conditional law. -/
theorem finite_oriented_singleLinkConditionalPMF_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge) :
    L.singleLinkConditionalPMF A target g =
      L.singleLinkBoltzmannWeight A target g *
        (L.singleLinkPartitionFunction A target)⁻¹ := by
  rfl

/-- Total variation between two exact oriented single-link conditional laws. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ g : L.Gauge,
    |(L.singleLinkConditionalPMF A target g).toReal -
      (L.singleLinkConditionalPMF B target g).toReal|

/-- Oriented single-link conditional total variation is nonnegative. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B target := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun g _hg => abs_nonneg _)

/-- Replacing the selected physical link erases differences already confined to
that link. -/
theorem finite_oriented_replaceLink_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (source : L.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    L.replaceLink A source g = L.replaceLink B source g := by
  classical
  funext e
  by_cases h : e = source
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h, hAgree e h]

/-- Oriented one-link Boltzmann weights depend only on off-link data. -/
theorem finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkBoltzmannWeight A target g =
      L.singleLinkBoltzmannWeight B target g := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
  rw [finite_oriented_replaceLink_eq_of_agreeOffLink L A B target g hAgree]

/-- Oriented one-link partition functions are constant on off-link fibers. -/
theorem finite_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkPartitionFunction A target =
      L.singleLinkPartitionFunction B target := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
  congr 1
  funext g
  exact finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    L A B target g hAgree

/-- The exact oriented conditional law is constant on off-link fibers. -/
theorem finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalPMF A target =
      L.singleLinkConditionalPMF B target := by
  ext g
  rw [finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
      L A B target g hAgree,
    finite_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
      L A B target hAgree]

/-- Self-link perturbations have exactly zero conditional total variation. -/
theorem finite_oriented_singleLinkConditionalTotalVariation_eq_zero_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalTotalVariation A B target = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  rw [finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
    L A B target hAgree]
  simp

/-- Exact conditional expectation obtained by resampling one physical link with
the orientation-correct Wilson conditional law. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge) : ℝ := by
  classical
  exact ∑ g : L.Gauge,
    (L.singleLinkConditionalPMF A target g).toReal *
      f (L.replaceLink A target g)

/-- Pointwise expansion of the oriented one-link conditional expectation. -/
theorem finite_oriented_singleLinkConditionalExpectation_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (target : L.Edge) :
    L.singleLinkConditionalExpectation f A target =
      ∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal *
          f (L.replaceLink A target g) := by
  rfl

/-- The oriented conditional expectation is constant on every off-target
configuration fiber. -/
theorem finite_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalExpectation f A target =
      L.singleLinkConditionalExpectation f B target := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B target hAgree,
    finite_oriented_replaceLink_eq_of_agreeOffLink
      L A B target g hAgree]

end

end MathlibAnalytic
end MGAP4D
