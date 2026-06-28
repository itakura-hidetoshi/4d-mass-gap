import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Replacing the selected physical link erases every difference between
configurations that already agree away from that link. -/
theorem finite_oriented_replaceLink_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e g = L.replaceLink B e g := by
  classical
  funext e'
  by_cases h : e' = e
  · subst e'
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, h, hAgree e' h]

/-- Updating one physical link twice retains only the last update. -/
@[simp] theorem finite_oriented_replaceLink_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (h g : L.Gauge) :
    L.replaceLink (L.replaceLink A e h) e g =
      L.replaceLink A e g := by
  classical
  funext e'
  by_cases he : e' = e
  · subst e'
    simp
  · simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]

/-- If two configurations agree away from one link, inserting the second
configuration's value at that link recovers the second configuration. -/
theorem finite_oriented_replaceLink_right_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e (B e) = B := by
  calc
    L.replaceLink A e (B e) =
        L.replaceLink B e (B e) :=
      finite_oriented_replaceLink_eq_of_agreeOffLink
        L A B e (B e) hAgree
    _ = B := finite_oriented_replaceLink_current L B e

/-- The exact oriented single-link Boltzmann weight depends only on the
configuration away from the updated physical link. -/
theorem finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkBoltzmannWeight A e g =
      L.singleLinkBoltzmannWeight B e g := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkBoltzmannWeight
  rw [finite_oriented_replaceLink_eq_of_agreeOffLink
    L A B e g hAgree]

/-- The exact oriented single-link partition function is invariant on every
off-link fiber. -/
theorem finite_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkPartitionFunction A e =
      L.singleLinkPartitionFunction B e := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
  congr 1
  funext g
  exact finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    L A B e g hAgree

/-- The exact oriented single-link conditional law depends only on the
configuration outside the updated physical link. -/
theorem finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalPMF A e =
      L.singleLinkConditionalPMF B e := by
  ext g
  rw [finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkConditionalPMF_apply,
    finite_oriented_singleLinkBoltzmannWeight_eq_of_agreeOffLink
      L A B e g hAgree,
    finite_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
      L A B e hAgree]

/-- Pre-updating the physical link being resampled does not alter its exact
conditional law. -/
theorem finite_oriented_singleLinkConditionalPMF_replaceLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (h : L.Gauge) :
    L.singleLinkConditionalPMF (L.replaceLink A e h) e =
      L.singleLinkConditionalPMF A e := by
  apply finite_oriented_singleLinkConditionalPMF_eq_of_agreeOffLink
  intro e' he
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, he]

end

end MathlibAnalytic
end MGAP4D
