import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorKernelBootstrapStep
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialIncidenceBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Sharing a spatial plaquette is symmetric on lower spatial links. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalNeighborhood_symmetric
    (H : ℕ)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    source ∈
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H target ↔
      target ∈
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H source := by
  simp only [
    finiteEvenFourTorusZ2_mem_perronSmoothedPosteriorLocalSourceNeighborhood,
    finiteEvenFourTorusZ2_mem_lowerSpatialInteractionNeighborhood]
  constructor
  · rintro ⟨p, hTarget, hSourceSupport⟩
    have hSource :
        FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p source :=
      (finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
        H p source).1 hSourceSupport
    exact ⟨p, hSource,
      (finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
        H p target).2 hTarget⟩
  · rintro ⟨p, hSource, hTargetSupport⟩
    have hTarget :
        FiniteEvenFourTorusSpatialPlaquetteTouchesLink H p target :=
      (finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
        H p target).1 hTargetSupport
    exact ⟨p, hTarget,
      (finiteEvenFourTorusZ2_lower_mem_augmentedSpatialPlaquetteSupport_iff
        H p source).2 hSource⟩

/-- A source in the local neighborhood is coded by one target-touching
plaquette and one of its four boundary positions. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source :
      ↥(finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
        H target)) :
    ↥(finiteEvenFourTorusSpatialPlaquettesTouchingLink H target) × Fin 4 := by
  have hNeighborhood :=
    (finiteEvenFourTorusZ2_mem_perronSmoothedPosteriorLocalSourceNeighborhood
      H target source.1).1 source.2
  have hWitness :=
    (finiteEvenFourTorusZ2_mem_lowerSpatialInteractionNeighborhood
      H target (Sum.inr source.1)).1 hNeighborhood
  let p : FiniteEvenFourTorusSpatialPlaquette H := Classical.choose hWitness
  have hp :=
    Classical.choose_spec hWitness
  have hpSet :
      p ∈ finiteEvenFourTorusSpatialPlaquettesTouchingLink H target :=
    (finiteEvenFourTorusSpatialPlaquette_mem_touchingLink_iff
      H target p).2 hp.1
  have hkImage :=
    Finset.mem_image.mp hp.2
  let k : Fin 4 := Classical.choose hkImage
  exact (⟨p, hpSet⟩, k)

/-- The local source code recovers the represented source link. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode_boundary
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (source :
      ↥(finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
        H target)) :
    finiteEvenFourTorusSpatialPlaquetteBoundary H
        (finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode
          H target source).1.1
        (finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode
          H target source).2 =
      source.1 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode
  simp only
  let hNeighborhood :=
    (finiteEvenFourTorusZ2_mem_perronSmoothedPosteriorLocalSourceNeighborhood
      H target source.1).1 source.2
  let hWitness :=
    (finiteEvenFourTorusZ2_mem_lowerSpatialInteractionNeighborhood
      H target (Sum.inr source.1)).1 hNeighborhood
  let p : FiniteEvenFourTorusSpatialPlaquette H := Classical.choose hWitness
  have hp := Classical.choose_spec hWitness
  have hkImage := Finset.mem_image.mp hp.2
  have hk := Classical.choose_spec hkImage
  exact Sum.inr.inj hk.2

/-- The local source code is injective. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode_injective
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    Function.Injective
      (finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode H target) := by
  intro source other hCode
  apply Subtype.ext
  have hBoundary := congrArg
    (fun code :
      ↥(finiteEvenFourTorusSpatialPlaquettesTouchingLink H target) × Fin 4 =>
      finiteEvenFourTorusSpatialPlaquetteBoundary H code.1.1 code.2)
    hCode
  have hBoundary' : source.1 = other.1 := by
    simpa only [
      finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode_boundary]
      using hBoundary
  exact hBoundary'

/-- Every local source neighborhood contains at most forty-eight links,
uniformly in the finite side parameter. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalSourceNeighborhood_card_le_fortyEight
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
      H target).card ≤ 48 := by
  let neighborhood :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
      H target
  let touching :=
    finiteEvenFourTorusSpatialPlaquettesTouchingLink H target
  have hInjective :
      Function.Injective
        (finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode H target) :=
    finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode_injective H target
  have hCard :
      Fintype.card ↥neighborhood ≤
        Fintype.card (↥touching × Fin 4) :=
    Fintype.card_le_of_injective
      (finiteEvenFourTorusZ2PerronPosteriorLocalSourceCode H target)
      hInjective
  have hTouching :
      touching.card ≤ 12 :=
    finiteEvenFourTorusSpatialPlaquettesTouchingLink_card_le_twelve H target
  calc
    neighborhood.card = Fintype.card ↥neighborhood := by simp
    _ ≤ Fintype.card (↥touching × Fin 4) := hCard
    _ = touching.card * 4 := by simp
    _ ≤ 12 * 4 := Nat.mul_le_mul_right 4 hTouching
    _ = 48 := by norm_num

/-- Uniform one-half-action influence majorant on a shared-plaquette source. -/
def finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
    (β energyIdentity energyNontrivial : ℝ) : ℝ :=
  finitePositiveWeightCrossRatioInfluenceTransform
    (12 * β * (energyNontrivial - energyIdentity))

/-- The local majorant is nonnegative at physical coupling. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant_nonneg
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
      β energyIdentity energyNontrivial := by
  exact finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
    (mul_nonneg
      (mul_nonneg (by norm_num) hβ)
      (sub_nonneg.mpr hEnergy))

/-- Every actual local influence entry is bounded by the uniform
shared-plaquette majorant. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalInfluence_le_majorant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source ≤
      if source ∈
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
            H target then
        finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
          β energyIdentity energyNontrivial
      else 0 := by
  by_cases hEq : target = source
  · subst source
    simp only [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence,
      if_pos rfl]
    by_cases hMem :
        target ∈
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
            H target
    · rw [if_pos hMem]
      exact
        finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant_nonneg
          β energyIdentity energyNontrivial hβ hEnergy
    · rw [if_neg hMem]
  · by_cases hMem :
      source ∈
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H target
    · rw [if_pos hMem]
      unfold
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
        finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
        finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
      have hAugmented :
          Sum.inr source ∈
            finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target := by
        simpa using hMem
      rw [if_neg hEq, if_pos hAugmented]
      exact le_rfl
    · rw [if_neg hMem]
      exact le_of_eq
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_eq_zero_of_not_mem
          H β energyIdentity energyNontrivial target source hMem)

/-- The actual local influence is symmetric in target and source. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalInfluence_symmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source =
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial source target := by
  by_cases hEq : target = source
  · subst source
    rfl
  · have hEq' : source ≠ target := Ne.symm hEq
    unfold
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
      finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
    rw [if_neg hEq, if_neg hEq']
    have hNeighborhood :
        Sum.inr source ∈
            finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target ↔
          Sum.inr target ∈
            finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H source := by
      simpa only [
        finiteEvenFourTorusZ2_mem_perronSmoothedPosteriorLocalSourceNeighborhood]
        using
          finiteEvenFourTorusZ2PerronPosteriorLocalNeighborhood_symmetric
            H target source
    by_cases hMem :
        Sum.inr source ∈
          finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target
    · rw [if_pos hMem, if_pos (hNeighborhood.mp hMem)]
    · have hMem' :
          Sum.inr target ∉
            finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H source :=
        (not_congr hNeighborhood).mp hMem
      rw [if_neg hMem, if_neg hMem']

/-- One local half-action row has a volume-independent coefficient
`48 * majorant`. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceRowSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
        H β energyIdentity energyNontrivial target ≤
      48 * finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
        β energyIdentity energyNontrivial := by
  let neighborhood :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
      H target
  let majorant :=
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
      β energyIdentity energyNontrivial
  have hMajorant : 0 ≤ majorant :=
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum_eq_support_sum]
  calc
    (∑ source ∈ neighborhood,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source) ≤
      ∑ _source ∈ neighborhood, majorant := by
        apply Finset.sum_le_sum
        intro source hSource
        simpa [majorant, neighborhood, hSource] using
          finiteEvenFourTorusZ2PerronPosteriorLocalInfluence_le_majorant
            H β energyIdentity energyNontrivial hβ hEnergy target source
    _ = (neighborhood.card : ℝ) * majorant := by
      simp [nsmul_eq_mul]
    _ ≤ 48 * majorant := by
      apply mul_le_mul_of_nonneg_right _ hMajorant
      exact_mod_cast
        finiteEvenFourTorusZ2PerronPosteriorLocalSourceNeighborhood_card_le_fortyEight
          H target

/-- The local influence column has the same uniform bound by symmetry. -/
theorem finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceColumnSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H) :
    (∑ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source) ≤
      48 * finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
        β energyIdentity energyNontrivial := by
  calc
    (∑ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source) =
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
        H β energyIdentity energyNontrivial source := by
        unfold
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
        apply Finset.sum_congr rfl
        intro target _hTarget
        exact
          finiteEvenFourTorusZ2PerronPosteriorLocalInfluence_symmetric
            H β energyIdentity energyNontrivial target source
    _ ≤ 48 * finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
        β energyIdentity energyNontrivial :=
      finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceRowSum_le
        H β energyIdentity energyNontrivial hβ hEnergy source

/-- The exact two-local-half-action kernel. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorTwoLocalKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteNonnegativeInfluenceKernelData
      (FiniteEvenFourTorusSpatialLink H) :=
  { influence := fun target source =>
      2 *
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
          H β energyIdentity energyNontrivial target source
    influence_nonneg := by
      intro target source
      exact mul_nonneg (by norm_num)
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_nonneg
          H β energyIdentity energyNontrivial hβ hEnergy target source)
    influence_diagonal_zero := by
      intro target
      simp [
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence] }

/-- The two-local kernel has explicit maximum column coefficient
`96 * majorant`. -/
theorem finiteEvenFourTorusZ2PerronPosteriorTwoLocalKernel_columnSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelColumnSum
        (finiteEvenFourTorusZ2PerronPosteriorTwoLocalKernel
          H β energyIdentity energyNontrivial hβ hEnergy)
        source ≤
      96 * finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
        β energyIdentity energyNontrivial := by
  unfold finiteInfluenceKernelColumnSum
    finiteEvenFourTorusZ2PerronPosteriorTwoLocalKernel
  rw [← Finset.mul_sum]
  have hLocal :=
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceColumnSum_le
      H β energyIdentity energyNontrivial hβ hEnergy source
  nlinarith

end

end MathlibAnalytic
end MGAP4D
