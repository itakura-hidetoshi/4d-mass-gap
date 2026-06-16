import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathVariance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two link configurations agree outside the selected update link. -/
def FiniteLatticeWilsonSystem.AgreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) : Prop :=
  ∀ e' : L.Edge, e' ≠ e → A e' = B e'

/-- Replacing the selected link erases every difference between configurations
that already agree away from that link. -/
theorem finite_lattice_replaceLink_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e g = L.replaceLink B e g := by
  classical
  funext e'
  by_cases h : e' = e
  · subst e'
    simp
  · simp [FiniteLatticeWilsonSystem.replaceLink, h, hAgree e' h]

/-- Updating one link twice retains only the last update. -/
@[simp] theorem finite_lattice_replaceLink_replaceLink
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (h g : L.Gauge) :
    L.replaceLink (L.replaceLink A e h) e g =
      L.replaceLink A e g := by
  classical
  funext e'
  by_cases he : e' = e
  · subst e'
    simp
  · simp [FiniteLatticeWilsonSystem.replaceLink, he]

/-- The single-link conditional Boltzmann weight depends only on the
configuration away from the updated link. -/
theorem finite_lattice_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge) (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkBoltzmannWeight A e g =
      L.singleLinkBoltzmannWeight B e g := by
  unfold FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight
  rw [finite_lattice_replaceLink_eq_of_agreeOffLink L A B e g hAgree]

/-- The single-link conditional partition function is constant on every fiber
of configurations with fixed off-link data. -/
theorem finite_lattice_singleLinkPartitionFunction_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkPartitionFunction A e =
      L.singleLinkPartitionFunction B e := by
  unfold FiniteLatticeWilsonSystem.singleLinkPartitionFunction
  congr 1
  funext g
  exact finite_lattice_singleLinkBoltzmannWeight_eq_of_agreeOffLink
    L A B e g hAgree

/-- The exact single-link conditional Gibbs law is a function only of the
configuration outside the updated link. -/
theorem finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalPMF A e =
      L.singleLinkConditionalPMF B e := by
  ext g
  rw [finite_lattice_singleLinkConditionalPMF_apply,
    finite_lattice_singleLinkConditionalPMF_apply,
    finite_lattice_singleLinkBoltzmannWeight_eq_of_agreeOffLink
      L A B e g hAgree,
    finite_lattice_singleLinkPartitionFunction_eq_of_agreeOffLink
      L A B e hAgree]

/-- In particular, the conditional law is unchanged when only the old value of
the updated link is modified. -/
theorem finite_lattice_singleLinkConditionalPMF_replaceLink
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge) :
    L.singleLinkConditionalPMF (L.replaceLink A e h) e =
      L.singleLinkConditionalPMF A e := by
  apply finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
  intro e' he
  simp [FiniteLatticeWilsonSystem.replaceLink, he]

/-- Single-link conditional expectation is constant on off-link fibers. -/
theorem finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalExpectation f A e =
      L.singleLinkConditionalExpectation f B e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalExpectation
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B e hAgree,
    finite_lattice_replaceLink_eq_of_agreeOffLink L A B e g hAgree]

/-- Single-link conditional variance is constant on off-link fibers. -/
theorem finite_lattice_singleLinkConditionalVariance_eq_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration) (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.singleLinkConditionalVariance f A e =
      L.singleLinkConditionalVariance f B e := by
  classical
  unfold FiniteLatticeWilsonSystem.singleLinkConditionalVariance
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finite_lattice_singleLinkConditionalPMF_eq_of_agreeOffLink
      L A B e hAgree,
    finite_lattice_replaceLink_eq_of_agreeOffLink L A B e g hAgree,
    finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
      L f A B e hAgree]

/-- Conditional expectation is unchanged by pre-updating the resampled link. -/
theorem finite_lattice_singleLinkConditionalExpectation_replaceLink
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge) :
    L.singleLinkConditionalExpectation f (L.replaceLink A e h) e =
      L.singleLinkConditionalExpectation f A e := by
  apply finite_lattice_singleLinkConditionalExpectation_eq_of_agreeOffLink
  intro e' he
  simp [FiniteLatticeWilsonSystem.replaceLink, he]

/-- Conditional variance is unchanged by pre-updating the resampled link. -/
theorem finite_lattice_singleLinkConditionalVariance_replaceLink
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) (e : L.Edge) (h : L.Gauge) :
    L.singleLinkConditionalVariance f (L.replaceLink A e h) e =
      L.singleLinkConditionalVariance f A e := by
  apply finite_lattice_singleLinkConditionalVariance_eq_of_agreeOffLink
  intro e' he
  simp [FiniteLatticeWilsonSystem.replaceLink, he]

end

end MathlibAnalytic
end MGAP4D
