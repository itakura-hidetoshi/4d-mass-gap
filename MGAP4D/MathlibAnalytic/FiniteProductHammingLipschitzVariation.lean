import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinRandomScanContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A real observable on a finite product is `1`-Lipschitz for the real
Hamming distance. -/
def FiniteProductHammingOneLipschitz
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (f : (ι → G) → ℝ) : Prop :=
  ∀ A B : ι → G,
    |f A - f B| ≤ finiteProductHammingDistanceReal A B

/-- Configurations agreeing away from one coordinate have real Hamming
distance at most one. -/
theorem finiteProductHammingDistanceReal_le_one_of_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (A B : ι → G)
    (source : ι)
    (hAgree : FiniteProductAgreeOff A B source) :
    finiteProductHammingDistanceReal A B ≤ 1 := by
  have hSubset :
      finiteProductDisagreementFinset A B ⊆ ({source} : Finset ι) := by
    intro i hi
    have hNe : A i ≠ B i := by
      simpa [finiteProductDisagreementFinset] using hi
    by_cases hEq : i = source
    · simpa [hEq]
    · exact (hNe (hAgree i hEq)).elim
  have hCard :
      (finiteProductDisagreementFinset A B).card ≤
        ({source} : Finset ι).card :=
    Finset.card_le_card hSubset
  unfold finiteProductHammingDistanceReal
  simpa using (show
    ((finiteProductDisagreementFinset A B).card : ℝ) ≤
      (({source} : Finset ι).card : ℝ) by
        exact_mod_cast hCard)

/-- Every Hamming `1`-Lipschitz observable has the constant-one declared
coordinate variation profile. -/
noncomputable def finiteProductHammingOneLipschitzVariationBound
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    FiniteProductVariationBound f :=
  { variation := fun _ => 1
    variation_nonneg := fun _ => by norm_num
    variation_bound := by
      intro source A B hAgree
      exact (hLipschitz A B).trans
        (finiteProductHammingDistanceReal_le_one_of_agreeOff
          A B source hAgree) }

@[simp] theorem finiteProductHammingOneLipschitzVariationBound_variation
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f)
    (source : ι) :
    (finiteProductHammingOneLipschitzVariationBound
      f hLipschitz).variation source = 1 := by
  rfl

/-- The total constant-one variation is exactly the number of product
coordinates. -/
theorem finiteProductHammingOneLipschitzVariationBound_total
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    finiteProductVariationTotal
      (finiteProductHammingOneLipschitzVariationBound
        f hLipschitz).variation =
      (Fintype.card ι : ℝ) := by
  unfold finiteProductVariationTotal
  simp

/-- Public generic package for Hamming `1`-Lipschitz observables and their
unit coordinate-variation profiles. -/
theorem finiteProductHammingOneLipschitzVariationPackage
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    (∀ source : ι,
      (finiteProductHammingOneLipschitzVariationBound
        f hLipschitz).variation source = 1) ∧
    finiteProductVariationTotal
      (finiteProductHammingOneLipschitzVariationBound
        f hLipschitz).variation =
      (Fintype.card ι : ℝ) := by
  exact ⟨
    finiteProductHammingOneLipschitzVariationBound_variation
      f hLipschitz,
    finiteProductHammingOneLipschitzVariationBound_total
      f hLipschitz⟩

end

end MathlibAnalytic
end MGAP4D
