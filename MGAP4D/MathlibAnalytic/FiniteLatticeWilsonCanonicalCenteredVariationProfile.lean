import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalFiberExtrema

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite set of exact single-link fiber ranges obtained by varying the
base configuration while keeping the selected link fixed. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableRanges
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : Finset ℝ := by
  classical
  letI : Fintype L.Configuration := Fintype.ofFinite L.Configuration
  exact Finset.univ.image (fun A : L.Configuration =>
    L.fiberObservableRange f A e)

/-- The finite set of fiber ranges is nonempty. -/
theorem finite_lattice_fiberObservableRanges_nonempty
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    (L.fiberObservableRanges f e).Nonempty := by
  classical
  refine ⟨L.fiberObservableRange f default e, ?_⟩
  simp [FiniteLatticeWilsonSystem.fiberObservableRanges]

/-- The canonical link variation is the largest exact fiber range over all
finite Wilson configurations. -/
noncomputable def FiniteLatticeWilsonSystem.canonicalLinkVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableRanges f e).max'
    (finite_lattice_fiberObservableRanges_nonempty L f e)

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
  simp [FiniteLatticeWilsonSystem.fiberObservableRanges]

/-- Canonical link variation is nonnegative. -/
theorem finite_lattice_canonicalLinkVariation_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge) :
    0 ≤ L.canonicalLinkVariation f e :=
  le_trans
    (finite_lattice_fiberObservableRange_nonneg L f default e)
    (finite_lattice_fiberObservableRange_le_canonicalLinkVariation
      L f default e)

/-- Replacing a link by its current value leaves the configuration unchanged. -/
@[simp] theorem finite_lattice_replaceLink_current
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge) :
    L.replaceLink A e (A e) = A := by
  classical
  funext e'
  by_cases h : e' = e
  · subst e'
    simp
  · simp [FiniteLatticeWilsonSystem.replaceLink, h]

/-- If two configurations agree away from one link, the second is obtained by
replacing that link in the first by the second link value. -/
theorem finite_lattice_replaceLink_right_of_agreeOffLink
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge)
    (hAgree : L.AgreeOffLink A B e) :
    L.replaceLink A e (B e) = B := by
  classical
  funext e'
  by_cases h : e' = e
  · subst e'
    simp
  · simp [FiniteLatticeWilsonSystem.replaceLink, h, hAgree e' h]

/-- The canonical variation bounds the oscillation of an arbitrary observable
between configurations differing at only the selected link. -/
theorem finite_lattice_canonicalLinkVariation_difference_abs_le
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B e) :
    |f A - f B| ≤ L.canonicalLinkVariation f e := by
  have hLocal :
      |f A - f B| ≤ L.fiberObservableRange f A e := by
    simpa [finite_lattice_replaceLink_current,
      finite_lattice_replaceLink_right_of_agreeOffLink L A B e hAgree] using
      (finite_lattice_fiberObservable_difference_abs_le_range
        L f A e (A e) (B e))
  exact le_trans hLocal
    (finite_lattice_fiberObservableRange_le_canonicalLinkVariation
      L f A e)

/-- The canonical midpoint on each fiber lies within half the canonical link
variation of every value on that fiber. -/
theorem finite_lattice_fiberObservable_abs_sub_center_le_half_canonicalVariation
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.canonicalLinkVariation f e / 2 := by
  calc
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
        L.fiberObservableRange f A e / 2 :=
      finite_lattice_fiberObservable_abs_sub_center_le_half_range
        L f A e g
    _ ≤ L.canonicalLinkVariation f e / 2 := by
      linarith [finite_lattice_fiberObservableRange_le_canonicalLinkVariation
        L f A e]

/-- Every finite Wilson observable carries a canonical centered variation
profile, with exact global fiber ranges and the midpoint of each local fiber. -/
noncomputable def
    FiniteLatticeWilsonSystem.canonicalCenteredVariationProfile
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    FiniteLatticeWilsonCenteredVariationProfile L f := by
  refine
    { variation := L.canonicalLinkVariation f
      variation_nonneg := finite_lattice_canonicalLinkVariation_nonneg L f
      variation_bound := ?_
      fiberCenter := L.fiberObservableCenter f
      fiber_radius_bound := ?_ }
  · intro e A B hAgree
    exact finite_lattice_canonicalLinkVariation_difference_abs_le
      L f e A B hAgree
  · intro A e g
    exact
      finite_lattice_fiberObservable_abs_sub_center_le_half_canonicalVariation
        L f A e g

/-- Patch into `A` the values of `B` on the finite set of selected links. -/
def FiniteLatticeWilsonSystem.configurationPatch
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge) : L.Configuration :=
  fun e => if e ∈ s then B e else A e

@[simp] theorem finite_lattice_configurationPatch_empty
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B ∅ = A := by
  funext e
  simp [FiniteLatticeWilsonSystem.configurationPatch]

@[simp] theorem finite_lattice_configurationPatch_univ
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B Finset.univ = B := by
  funext e
  simp [FiniteLatticeWilsonSystem.configurationPatch]

/-- Adding one selected link to a patch changes no other link. -/
theorem finite_lattice_configurationPatch_agreeOffLink_insert
    (L : FiniteLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge)
    (e : L.Edge) :
    L.AgreeOffLink
      (L.configurationPatch A B s)
      (L.configurationPatch A B (insert e s)) e := by
  intro e' hne
  simp [FiniteLatticeWilsonSystem.configurationPatch, hne]

/-- Zero canonical variation at one link forces invariance under every change
supported on that link. -/
theorem finite_lattice_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B e)
    (hZero : L.canonicalLinkVariation f e = 0) :
    f A = f B := by
  have hBound : |f A - f B| ≤ 0 := by
    simpa [hZero] using
      (finite_lattice_canonicalLinkVariation_difference_abs_le
        L f e A B hAgree)
  have hAbs : |f A - f B| = 0 :=
    le_antisymm hBound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

/-- If all canonical link variations vanish, the observable is constant on the
whole finite configuration space. -/
theorem finite_lattice_observable_eq_of_all_canonicalVariations_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0)
    (A B : L.Configuration) :
    f A = f B := by
  classical
  have hPatch :
      ∀ s : Finset L.Edge,
        f (L.configurationPatch A B s) = f A := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih =>
        calc
          f (L.configurationPatch A B (insert e s)) =
              f (L.configurationPatch A B s) := by
            symm
            exact
              finite_lattice_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
                L f e
                (L.configurationPatch A B s)
                (L.configurationPatch A B (insert e s))
                (finite_lattice_configurationPatch_agreeOffLink_insert
                  L A B s e)
                (hZero e)
          _ = f A := ih
  simpa using (hPatch Finset.univ).symm

/-- Joint vanishing of canonical link variations characterizes constants. -/
theorem finite_lattice_observable_eq_const_of_all_canonicalVariations_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0) :
    f = fun _ : L.Configuration => f default := by
  funext A
  exact finite_lattice_observable_eq_of_all_canonicalVariations_eq_zero
    L f hZero A default

end

end MathlibAnalytic
end MGAP4D
