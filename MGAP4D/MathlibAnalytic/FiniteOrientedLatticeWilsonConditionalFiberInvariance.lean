import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Replacing the selected physical link erases differences already confined to that link. -/
theorem finite_oriented_replaceLink_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) (source : L.Edge) (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    L.replaceLink A source g = L.replaceLink B source g := by
  classical
  funext e
  by_cases h : e = source
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h, hAgree e h]

/-- Every off-source fiber point is a source replacement. -/
theorem finite_oriented_replaceLink_right_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) (source : L.Edge)
    (hAgree : L.AgreeOffLink A B source) :
    L.replaceLink A source (B source) = B := by
  classical
  funext e
  by_cases h : e = source
  · subst e
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h, hAgree e h]

/-- Oriented one-link Boltzmann weights depend only on off-link data. -/
theorem finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) (target : L.Edge) (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkBoltzmannWeight A target g =
      L.singleLinkBoltzmannWeight B target g := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
  rw [finite_oriented_replaceLink_eq_of_agreeOffLink L A B target g hAgree]

/-- Oriented one-link partition functions are constant on off-link fibers. -/
theorem finite_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) (target : L.Edge)
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
    (A B : L.Configuration) (target : L.Edge)
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
    (A B : L.Configuration) (target : L.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.singleLinkConditionalTotalVariation A B target = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalTotalVariation
  rw [finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
    L A B target hAgree]
  simp

end

end MathlibAnalytic
end MGAP4D
