import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanConditionalAverage
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite set of observable values obtained by varying one physical link
while freezing every other link. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableValues
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : Finset ℝ :=
  Finset.univ.image (fun g : L.Gauge => f (L.replaceLink A e g))

/-- Every one-link observable fiber is nonempty because the finite gauge group
is inhabited. -/
theorem finite_oriented_fiberObservableValues_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    (L.fiberObservableValues f A e).Nonempty := by
  classical
  refine ⟨f (L.replaceLink A e default), ?_⟩
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

/-- Maximum value of an observable on a one-link fiber. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableMax
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).max'
    (finite_oriented_fiberObservableValues_nonempty L f A e)

/-- Minimum value of an observable on a one-link fiber. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableMin
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).min'
    (finite_oriented_fiberObservableValues_nonempty L f A e)

/-- Every fiber value lies below the fiber maximum. -/
theorem finite_oriented_fiberObservableValue_le_max
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    f (L.replaceLink A e g) ≤ L.fiberObservableMax f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
  apply Finset.le_max'
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

/-- The fiber minimum lies below every fiber value. -/
theorem finite_oriented_fiberObservableMin_le_value
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.fiberObservableMin f A e ≤ f (L.replaceLink A e g) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
  apply Finset.min'_le
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

/-- Diameter of the finite one-link observable fiber. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableRange
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  L.fiberObservableMax f A e - L.fiberObservableMin f A e

/-- A one-link fiber diameter is nonnegative. -/
theorem finite_oriented_fiberObservableRange_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    0 ≤ L.fiberObservableRange f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
  exact sub_nonneg.mpr
    (Finset.min'_le_max'
      (L.fiberObservableValues f A e)
      (finite_oriented_fiberObservableValues_nonempty L f A e))

/-- Midpoint of the minimum and maximum values on a one-link fiber. -/
noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableCenter
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableMin f A e + L.fiberObservableMax f A e) / 2

/-- Every fiber value lies within half the fiber diameter of its midpoint. -/
theorem finite_oriented_fiberObservable_abs_sub_center_le_half_range
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.fiberObservableRange f A e / 2 := by
  have hMin := finite_oriented_fiberObservableMin_le_value L f A e g
  have hMax := finite_oriented_fiberObservableValue_le_max L f A e g
  rw [abs_le]
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableCenter
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange
  constructor <;> linarith

/-- Any two replacements of the same physical link agree away from that link. -/
theorem finite_oriented_replaceLink_pair_agreeOffLink
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (g h : L.Gauge) :
    L.AgreeOffLink (L.replaceLink A e g) (L.replaceLink A e h) e := by
  intro e' hne
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hne]

/-- A proof-relevant link-variation bound controls the diameter of every
one-link fiber. -/
theorem finite_oriented_fiberObservableRange_le_linkVariationBound
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A : L.Configuration)
    (e : L.Edge) :
    L.fiberObservableRange f A e ≤ P.variation e := by
  classical
  have hMaxExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMax f A e := by
    have hMem :
        L.fiberObservableMax f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
      exact Finset.max'_mem _ _
    simpa [FiniteOrientedLatticeWilsonSystem.fiberObservableValues] using hMem
  have hMinExists :
      ∃ g : L.Gauge,
        f (L.replaceLink A e g) = L.fiberObservableMin f A e := by
    have hMem :
        L.fiberObservableMin f A e ∈ L.fiberObservableValues f A e := by
      unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
      exact Finset.min'_mem _ _
    simpa [FiniteOrientedLatticeWilsonSystem.fiberObservableValues] using hMem
  rcases hMaxExists with ⟨gMax, hMax⟩
  rcases hMinExists with ⟨gMin, hMin⟩
  have hBound :=
    P.variation_bound e
      (L.replaceLink A e gMax)
      (L.replaceLink A e gMin)
      (finite_oriented_replaceLink_pair_agreeOffLink
        L A e gMax gMin)
  have hRangeNonneg :=
    finite_oriented_fiberObservableRange_nonneg L f A e
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange at hRangeNonneg ⊢
  calc
    L.fiberObservableMax f A e - L.fiberObservableMin f A e =
        |L.fiberObservableMax f A e - L.fiberObservableMin f A e| :=
      (abs_of_nonneg hRangeNonneg).symm
    _ = |f (L.replaceLink A e gMax) -
          f (L.replaceLink A e gMin)| := by
      rw [hMax, hMin]
    _ ≤ P.variation e := hBound

/-- The midpoint center reconstructed from a link-variation bound has the
required half-variation radius. -/
theorem finite_oriented_fiberObservable_abs_sub_center_le_half_variation
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      P.variation e / 2 := by
  calc
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
        L.fiberObservableRange f A e / 2 :=
      finite_oriented_fiberObservable_abs_sub_center_le_half_range
        L f A e g
    _ ≤ P.variation e / 2 := by
      linarith [finite_oriented_fiberObservableRange_le_linkVariationBound
        L f P A e]

/-- Recenter any nonnegative proof-relevant link-variation bound by taking the
midpoint of the finite minimum and maximum on each one-link fiber. -/
noncomputable def
    FiniteOrientedLatticeWilsonLinkVariationBound.centeredVariationProfile
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile L f :=
  { variation := P.variation
    variation_nonneg := P.variation_nonneg
    variation_bound := P.variation_bound
    fiberCenter := L.fiberObservableCenter f
    fiber_radius_bound := by
      intro A e g
      exact finite_oriented_fiberObservable_abs_sub_center_le_half_variation
        L f P A e g }

@[simp] theorem
    FiniteOrientedLatticeWilsonLinkVariationBound.centeredVariationProfile_variation
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (e : L.Edge) :
    P.centeredVariationProfile.variation e = P.variation e := rfl

/-- Recenter the concrete random-scan variation certificate so that it can be
fed back into the one-link Dobrushin propagation theorem. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageCenteredVariationProfile
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile L
      (L.randomScanConditionalAverage f) :=
  (P.randomScanConditionalAverageVariationBound D).centeredVariationProfile

/-- Recentering preserves the explicit random-scan contraction estimate because
it does not alter the variation function. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageCenteredVariation_sum_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    (∑ source : L.Edge,
      (P.randomScanConditionalAverageCenteredVariationProfile D).variation source) ≤
      finiteOrientedConditionalAverageRandomScanContractionFactor D *
        ∑ source : L.Edge, P.variation source := by
  exact P.randomScanConditionalAverageVariation_sum_le D hEdge

/-- The periodic `Z₂` plaquette random-scan observable therefore carries a
centered profile suitable for another Dobrushin random-scan step. -/
noncomputable def
    z2PeriodicHypercubicOrientedPlaquetteRandomScanCenteredVariationProfile
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        |>.randomScanConditionalAverage
          ((z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
            |>.plaquetteObservable p)) :=
  (z2PeriodicHypercubicOrientedPlaquetteRandomScanVariationBound
    n beta hBeta p D).centeredVariationProfile

end

end MathlibAnalytic
end MGAP4D
