import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonPlaquetteRandomScanVariationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Patch a finite set of physical links of `A` with the corresponding values
from `B`.  This is the telescoping path used to turn one-link variation bounds
into an all-configuration oscillation bound. -/
def FiniteOrientedLatticeWilsonSystem.linkVariationConfigurationPatch
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (s : Finset L.Edge) : L.Configuration := by
  classical
  exact fun e => if e ∈ s then B e else A e

@[simp] theorem finite_oriented_linkVariationConfigurationPatch_empty
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.linkVariationConfigurationPatch A B ∅ = A := by
  classical
  funext e
  simp [FiniteOrientedLatticeWilsonSystem.linkVariationConfigurationPatch]

@[simp] theorem finite_oriented_linkVariationConfigurationPatch_univ
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration) :
    L.linkVariationConfigurationPatch A B Finset.univ = B := by
  classical
  funext e
  simp [FiniteOrientedLatticeWilsonSystem.linkVariationConfigurationPatch]

/-- Adding one link to a patch changes no physical link other than the newly
inserted link. -/
theorem finite_oriented_linkVariationConfigurationPatch_agreeOffLink_insert
    (L : FiniteOrientedLatticeWilsonSystem)
    [DecidableEq L.Edge]
    (A B : L.Configuration)
    (s : Finset L.Edge)
    (e : L.Edge) :
    L.AgreeOffLink
      (L.linkVariationConfigurationPatch A B s)
      (L.linkVariationConfigurationPatch A B (insert e s)) e := by
  intro e' hne
  unfold FiniteOrientedLatticeWilsonSystem.linkVariationConfigurationPatch
  by_cases hs : e' ∈ s
  · have hInsert : e' ∈ insert e s := Finset.mem_insert_of_mem hs
    simp [hs, hInsert]
  · have hInsert : e' ∉ insert e s := by
      simp [hne, hs]
    simp [hs, hInsert]

/-- A proof-relevant one-link variation certificate controls the change from a
configuration to any finite patch by the sum of the variations on the patched
links. -/
theorem
    FiniteOrientedLatticeWilsonLinkVariationBound.abs_sub_linkVariationConfigurationPatch_le_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A B : L.Configuration)
    (s : Finset L.Edge) :
    |f A - f (L.linkVariationConfigurationPatch A B s)| ≤
      ∑ e ∈ s, P.variation e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
      have hStep :
          |f (L.linkVariationConfigurationPatch A B s) -
              f (L.linkVariationConfigurationPatch A B (insert e s))| ≤
            P.variation e :=
        P.variation_bound e
          (L.linkVariationConfigurationPatch A B s)
          (L.linkVariationConfigurationPatch A B (insert e s))
          (finite_oriented_linkVariationConfigurationPatch_agreeOffLink_insert
            L A B s e)
      calc
        |f A - f (L.linkVariationConfigurationPatch A B (insert e s))| =
            |(f A - f (L.linkVariationConfigurationPatch A B s)) +
              (f (L.linkVariationConfigurationPatch A B s) -
                f (L.linkVariationConfigurationPatch A B (insert e s)))| := by
          congr 1
          ring
        _ ≤ |f A - f (L.linkVariationConfigurationPatch A B s)| +
              |f (L.linkVariationConfigurationPatch A B s) -
                f (L.linkVariationConfigurationPatch A B (insert e s))| :=
          abs_add_le _ _
        _ ≤ (∑ source ∈ s, P.variation source) + P.variation e :=
          add_le_add ih hStep
        _ = ∑ source ∈ insert e s, P.variation source := by
          rw [Finset.sum_insert he]
          ring

/-- Summing a proof-relevant link-variation certificate over every physical
link bounds the observable difference between arbitrary configurations. -/
theorem FiniteOrientedLatticeWilsonLinkVariationBound.abs_sub_le_sum_variation
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A B : L.Configuration) :
    |f A - f B| ≤ ∑ e : L.Edge, P.variation e := by
  have h := P.abs_sub_linkVariationConfigurationPatch_le_sum A B Finset.univ
  simpa using h

/-- The proof-relevant profile carried by the `k`th random-scan observable
iterate bounds its actual all-configuration oscillation by its total variation
mass. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageIterate_abs_sub_le_sum_variation
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (k : ℕ)
    (A B : L.Configuration) :
    |L.randomScanConditionalAverageIterate f k A -
        L.randomScanConditionalAverageIterate f k B| ≤
      ∑ source : L.Edge,
        P.randomScanConditionalAverageVariationIterate D k source := by
  exact
    (P.randomScanConditionalAverageCenteredVariationIterate D k)
      |>.toFiniteOrientedLatticeWilsonLinkVariationBound
      |>.abs_sub_le_sum_variation A B

/-- The `k`th random-scan iterate of a selected periodic `Z₂` plaquette
observable has global configuration oscillation at most `4 q^k`. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanObservableIterate_oscillation_le_four_mul_pow
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (k : ℕ)
    (A B :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration) :
    |(z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverageIterate
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p) k A -
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverageIterate
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p) k B| ≤
      4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
  calc
    |(z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverageIterate
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p) k A -
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverageIterate
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p) k B| ≤
        ∑ source : PeriodicHypercubicEdge n,
          (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
            n beta hBeta p).randomScanConditionalAverageVariationIterate
              D k source :=
      (z2PeriodicHypercubicOrientedPlaquetteCenteredVariationProfile
        n beta hBeta p)
        |>.randomScanConditionalAverageIterate_abs_sub_le_sum_variation
          D k A B
    _ ≤ 4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k :=
      z2PeriodicHypercubicOrientedPlaquetteRandomScanVariationIterate_sum_le_four_mul_pow
        n beta hBeta p D k

end

end MathlibAnalytic
end MGAP4D
