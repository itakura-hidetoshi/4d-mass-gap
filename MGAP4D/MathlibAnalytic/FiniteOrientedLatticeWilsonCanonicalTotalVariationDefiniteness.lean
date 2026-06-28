import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalVariationMinimality
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathProjection
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsRealVariance
import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinTotalVariationContraction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def FiniteOrientedLatticeWilsonSystem.configurationPatch
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge) : L.Configuration := by
  classical
  exact fun e => if e ∈ s then B e else A e

@[simp] theorem finite_oriented_configurationPatch_empty
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B ∅ = A := by
  classical
  funext e
  simp [FiniteOrientedLatticeWilsonSystem.configurationPatch]

@[simp] theorem finite_oriented_configurationPatch_univ
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.configurationPatch A B Finset.univ = B := by
  classical
  funext e
  simp [FiniteOrientedLatticeWilsonSystem.configurationPatch]

theorem finite_oriented_configurationPatch_agreeOffLink_insert
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge)
    (e : L.Edge) :
    L.AgreeOffLink
      (L.configurationPatch A B s)
      (L.configurationPatch A B (insert e s)) e := by
  classical
  intro e' hne
  by_cases hs : e' ∈ s
  · simp [FiniteOrientedLatticeWilsonSystem.configurationPatch, hs]
  · have hInsert : e' ∉ insert e s := by simp [hne, hs]
    simp [FiniteOrientedLatticeWilsonSystem.configurationPatch, hs, hInsert]

theorem finite_oriented_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (A B : L.Configuration)
    (hAgree : L.AgreeOffLink A B e)
    (hZero : L.canonicalLinkVariation f e = 0) :
    f A = f B := by
  have hBound : |f A - f B| ≤ 0 := by
    simpa [hZero] using
      (finite_oriented_canonicalLinkVariation_difference_abs_le
        L f e A B hAgree)
  have hAbs : |f A - f B| = 0 :=
    le_antisymm hBound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hAbs)

theorem finite_oriented_observable_eq_of_all_canonicalVariations_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0)
    (A B : L.Configuration) :
    f A = f B := by
  classical
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
            finite_oriented_observable_eq_of_agreeOffLink_of_canonicalVariation_eq_zero
              L f e
              (L.configurationPatch A B s)
              (L.configurationPatch A B (insert e s))
              (finite_oriented_configurationPatch_agreeOffLink_insert
                L A B s e)
              (hZero e)
  simpa using hPatch Finset.univ

theorem finite_oriented_observable_eq_const_of_all_canonicalVariations_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hZero : ∀ e : L.Edge, L.canonicalLinkVariation f e = 0) :
    f = fun _ : L.Configuration => f default := by
  funext A
  exact finite_oriented_observable_eq_of_all_canonicalVariations_eq_zero
    L f hZero A default

theorem finite_oriented_gibbsExpectationReal_const
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ) :
    L.gibbsExpectationReal (fun _ : L.Configuration => c) = c := by
  classical
  letI : Fintype L.Configuration := Fintype.ofFinite L.Configuration
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  calc
    (∑ A : L.Configuration, (L.gibbsPMF A).toReal * c) =
        (∑ A : L.Configuration, (L.gibbsPMF A).toReal) * c := by
      rw [Finset.sum_mul]
    _ = c := by
      rw [finite_pmf_sum_toReal_eq_one]
      simp

def FiniteOrientedLatticeWilsonSystem.canonicalTotalVariation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  finiteOrientedLatticeWilsonTotalVariation (L.canonicalLinkVariation f)

theorem finite_oriented_canonicalTotalVariation_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.canonicalTotalVariation f := by
  unfold FiniteOrientedLatticeWilsonSystem.canonicalTotalVariation
    finiteOrientedLatticeWilsonTotalVariation
  exact Finset.sum_nonneg fun e _ =>
    finite_oriented_canonicalLinkVariation_nonneg L f e

theorem finite_oriented_canonicalLinkVariation_const_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (e : L.Edge) :
    L.canonicalLinkVariation (fun _ : L.Configuration => c) e = 0 := by
  let P : FiniteOrientedLatticeWilsonLinkVariationBound L
      (fun _ : L.Configuration => c) :=
    { variation := fun _ => 0
      variation_nonneg := fun _ => le_rfl
      variation_bound := by intro source A B hAgree; simp }
  exact le_antisymm
    (finite_oriented_canonicalLinkVariation_le_linkVariationBound
      L (fun _ : L.Configuration => c) P e)
    (finite_oriented_canonicalLinkVariation_nonneg
      L (fun _ : L.Configuration => c) e)

theorem finite_oriented_canonicalTotalVariation_const_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ) :
    L.canonicalTotalVariation (fun _ : L.Configuration => c) = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.canonicalTotalVariation
    finiteOrientedLatticeWilsonTotalVariation
  apply Finset.sum_eq_zero
  intro e _he
  exact finite_oriented_canonicalLinkVariation_const_eq_zero L c e

theorem finite_oriented_all_canonicalLinkVariations_eq_zero_of_total_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hTotal : L.canonicalTotalVariation f = 0) :
    ∀ e : L.Edge, L.canonicalLinkVariation f e = 0 := by
  intro e
  unfold FiniteOrientedLatticeWilsonSystem.canonicalTotalVariation
    finiteOrientedLatticeWilsonTotalVariation at hTotal
  have hEach :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun e' (_he' : e' ∈ (Finset.univ : Finset L.Edge)) =>
        finite_oriented_canonicalLinkVariation_nonneg L f e')).mp hTotal
  exact hEach e (Finset.mem_univ e)

theorem finite_oriented_canonicalTotalVariation_eq_zero_iff_const
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.canonicalTotalVariation f = 0 ↔
      f = fun _ : L.Configuration => f default := by
  constructor
  · intro hTotal
    exact finite_oriented_observable_eq_const_of_all_canonicalVariations_eq_zero
      L f
      (finite_oriented_all_canonicalLinkVariations_eq_zero_of_total_eq_zero
        L f hTotal)
  · intro hConst
    rw [hConst]
    exact finite_oriented_canonicalTotalVariation_const_eq_zero
      L (f default)

theorem finite_oriented_centered_observable_eq_zero_of_canonicalTotalVariation_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hMean : L.gibbsExpectationReal f = 0)
    (hTotal : L.canonicalTotalVariation f = 0) :
    f = 0 := by
  have hConst :=
    (finite_oriented_canonicalTotalVariation_eq_zero_iff_const L f).mp hTotal
  have hValue : f default = 0 := by
    rw [hConst, finite_oriented_gibbsExpectationReal_const] at hMean
    exact hMean
  rw [hConst, hValue]
  rfl

end
end MathlibAnalytic
end MGAP4D
