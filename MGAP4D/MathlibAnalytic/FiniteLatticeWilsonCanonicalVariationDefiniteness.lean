import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonCanonicalCenteredVariationProfile
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertRealization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite Wilson links admit classical decidable equality for finite patching. -/
noncomputable instance finiteLatticeWilsonEdgeDecidableEq
    (L : FiniteLatticeWilsonSystem) : DecidableEq L.Edge :=
  Classical.decEq L.Edge

/-- Patch into `A` the values of `B` on the selected finite set of links. -/
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
  by_cases hs : e' ∈ s
  · simp [FiniteLatticeWilsonSystem.configurationPatch, hs]
  · have hInsert : e' ∉ insert e s := by
      simp [hne, hs]
    simp [FiniteLatticeWilsonSystem.configurationPatch, hs, hInsert]

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
whole finite Wilson configuration space. -/
theorem finite_lattice_observable_eq_of_all_canonicalVariations_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0)
    (A B : L.Configuration) :
    f A = f B := by
  have hPatch :
      ∀ s : Finset L.Edge,
        f A = f (L.configurationPatch A B s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih =>
        calc
          f A = f (L.configurationPatch A B s) := ih
          _ = f (L.configurationPatch A B (insert e s)) :=
            finite_lattice_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
              L f e
              (L.configurationPatch A B s)
              (L.configurationPatch A B (insert e s))
              (finite_lattice_configurationPatch_agreeOffLink_insert
                L A B s e)
              (hZero e)
  simpa using hPatch Finset.univ

/-- Joint vanishing of canonical link variations characterizes constants. -/
theorem finite_lattice_observable_eq_const_of_all_canonicalVariations_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0) :
    f = fun _ : L.Configuration => f default := by
  funext A
  exact finite_lattice_observable_eq_of_all_canonicalVariations_eq_zero
    L f hZero A default

/-- Gibbs expectation preserves constant observables. -/
theorem finite_lattice_gibbsExpectationReal_const
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) :
    L.gibbsExpectationReal (fun _ : L.Configuration => c) = c := by
  have hEmbedConst :
      L.gibbsHilbertEmbedLinearMap (fun _ : L.Configuration => c) =
        c • L.gibbsHilbertVacuum := by
    rw [FiniteLatticeWilsonSystem.gibbsHilbertVacuum]
    ext A
    change Real.sqrt (L.gibbsProbabilityReal A) * c =
      c * (Real.sqrt (L.gibbsProbabilityReal A) * 1)
    ring
  calc
    L.gibbsExpectationReal (fun _ : L.Configuration => c) =
        inner ℝ L.gibbsHilbertVacuum
          (L.gibbsHilbertEmbedLinearMap
            (fun _ : L.Configuration => c)) :=
      (finite_lattice_gibbsHilbert_inner_vacuum_embed
        L (fun _ : L.Configuration => c)).symm
    _ = inner ℝ L.gibbsHilbertVacuum
        (c • L.gibbsHilbertVacuum) := by rw [hEmbedConst]
    _ = c := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq,
        finite_lattice_gibbsHilbertVacuum_norm]
      norm_num

/-- On the Gibbs-centered sector, the canonical link variations have trivial
joint kernel. -/
theorem finite_lattice_centered_observable_eq_zero_of_all_canonicalVariations_eq_zero
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0) :
    f = 0 := by
  have hConst :=
    finite_lattice_observable_eq_const_of_all_canonicalVariations_eq_zero
      L f hZero
  have hValue : f default = 0 := by
    rw [hConst, finite_lattice_gibbsExpectationReal_const] at hMean
    exact hMean
  rw [hConst, hValue]
  rfl

end

end MathlibAnalytic
end MGAP4D
