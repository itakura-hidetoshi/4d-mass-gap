import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalFiberExtrema

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite set of all single-link fiber ranges of `f` at a fixed link. -/
noncomputable def FiniteLatticeWilsonSystem.linkFiberRangeValues
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : Finset ℝ :=
  Finset.univ.image (fun A : L.Configuration =>
    L.fiberObservableRange f A e)

/-- The set of fiber ranges at a fixed link is nonempty. -/
theorem finite_lattice_linkFiberRangeValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    (L.linkFiberRangeValues f e).Nonempty := by
  classical
  refine ⟨L.fiberObservableRange f default e, ?_⟩
  simp [FiniteLatticeWilsonSystem.linkFiberRangeValues]

/-- The canonical link variation is the largest exact fiber range over all
finite configurations. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalLinkVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ :=
  (L.linkFiberRangeValues f e).max'
    (finite_lattice_linkFiberRangeValues_nonempty L f e)

/-- Every exact fiber range is bounded by the canonical link variation. -/
theorem finite_lattice_fiberObservableRange_le_canonicalLinkVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    L.fiberObservableRange f A e ≤ L.canonicalLinkVariation f e := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalLinkVariation
  apply Finset.le_max'
  simp [FiniteLatticeWilsonSystem.linkFiberRangeValues]

/-- The canonical link variation is nonnegative. -/
theorem finite_lattice_canonicalLinkVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    0 ≤ L.canonicalLinkVariation f e := by
  exact le_trans
    (finite_lattice_fiberObservableRange_nonneg L f default e)
    (finite_lattice_fiberObservableRange_le_canonicalLinkVariation
      L f default e)

/-- Replacing a link by its existing value leaves the configuration unchanged. -/
theorem finite_lattice_replaceLink_current
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge) :
    L.replaceLink A e (A e) = A := by
  classical
  funext x
  by_cases hx : x = e
  · subst x
    simp [FiniteLatticeWilsonSystem.replaceLink]
  · simp [FiniteLatticeWilsonSystem.replaceLink, hx]

/-- If `A` and `B` agree away from `e`, then `B` is obtained from `A` by
replacing the value at `e` by `B e`. -/
theorem finite_lattice_replaceLink_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e (B e) = B := by
  classical
  funext x
  by_cases hx : x = e
  · subst x
    simp [FiniteLatticeWilsonSystem.replaceLink]
  · simp [FiniteLatticeWilsonSystem.replaceLink, hx, hAgree x hx]

/-- The canonical link variation bounds the difference of any two
configurations that agree away from that link. -/
theorem finite_lattice_observable_difference_abs_le_canonicalLinkVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    |f A - f B| ≤ L.canonicalLinkVariation f e := by
  have hFiber :=
    finite_lattice_fiberObservable_difference_abs_le_range
      L f A e (A e) (B e)
  have hA := finite_lattice_replaceLink_current L A e
  have hB := finite_lattice_replaceLink_of_agreeOffLink L A B e hAgree
  rw [hA, hB] at hFiber
  exact le_trans hFiber
    (finite_lattice_fiberObservableRange_le_canonicalLinkVariation
      L f A e)

/-- Every fiber value lies within half the canonical link variation of the
canonical fiber midpoint. -/
theorem finite_lattice_fiberObservable_abs_sub_center_le_half_canonicalLinkVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.canonicalLinkVariation f e / 2 := by
  have hLocal :=
    finite_lattice_fiberObservable_abs_sub_center_le_half_range
      L f A e g
  have hRange :=
    finite_lattice_fiberObservableRange_le_canonicalLinkVariation
      L f A e
  exact le_trans hLocal (by linarith)

/-- The canonical centered variation profile of an arbitrary real observable
on a finite Wilson configuration space.  No external oscillation profile is
required. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalCenteredVariationProfile
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    FiniteLatticeWilsonCenteredVariationProfile L f :=
  { variation := L.canonicalLinkVariation f
    variation_nonneg := finite_lattice_canonicalLinkVariation_nonneg L f
    variation_bound := by
      intro e A B hAgree
      exact finite_lattice_observable_difference_abs_le_canonicalLinkVariation
        L f A B e hAgree
    fiberCenter := L.fiberObservableCenter f
    fiber_radius_bound := by
      intro A e g
      exact finite_lattice_fiberObservable_abs_sub_center_le_half_canonicalLinkVariation
        L f A e g }

end

end MathlibAnalytic
end MGAP4D
