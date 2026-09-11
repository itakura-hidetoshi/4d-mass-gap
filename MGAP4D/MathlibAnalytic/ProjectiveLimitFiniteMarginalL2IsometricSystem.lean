import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

variable
    {ι : Type*}
    {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]

/-- Coordinate restriction from a projective-limit configuration to one finite
marginal is measure preserving. -/
def projectiveLimitRestrictionMeasurePreserving
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι) :
    MeasurePreserving J.restrict μ (Q J) where
  measurable := J.measurable_restrict
  map_eq := hLimit J

/-- Restriction from a larger finite marginal to a smaller one is measure
preserving whenever the finite-dimensional laws form a projective family. -/
def projectiveFamilyRestrictionMeasurePreserving
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hProjective : IsProjectiveMeasureFamily Q)
    {I J : Finset ι}
    (hJI : J ⊆ I) :
    MeasurePreserving
      (Finset.restrict₂ hJI : (∀ i : I, α i) → (∀ i : J, α i))
      (Q I) (Q J) where
  measurable := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  map_eq := (hProjective I J hJI).symm

/-- Pullback along a projective-limit coordinate restriction gives a canonical
real-linear isometric embedding of each finite marginal `L²` space into the
continuum `L²` space. -/
noncomputable def projectiveLimitFiniteMarginalL2Pullback
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι) :
    Lp ℝ 2 (Q J) →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ J.restrict
    (projectiveLimitRestrictionMeasurePreserving μ Q hLimit J)

/-- Pullback along a restriction between two finite marginals is likewise a
canonical real-linear isometric embedding. -/
noncomputable def projectiveFamilyFiniteMarginalL2Pullback
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hProjective : IsProjectiveMeasureFamily Q)
    {I J : Finset ι}
    (hJI : J ⊆ I) :
    Lp ℝ 2 (Q J) →ₗᵢ[ℝ] Lp ℝ 2 (Q I) :=
  Lp.compMeasurePreservingₗᵢ ℝ (Finset.restrict₂ hJI)
    (projectiveFamilyRestrictionMeasurePreserving Q hProjective hJI)

@[simp] theorem projectiveLimitFiniteMarginalL2Pullback_norm
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι)
    (f : Lp ℝ 2 (Q J)) :
    ‖projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

@[simp] theorem projectiveLimitFiniteMarginalL2Pullback_inner
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι)
    (f g : Lp ℝ 2 (Q J)) :
    inner ℝ
        (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f)
        (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J g) =
      inner ℝ f g :=
  LinearIsometry.inner_map_map _ f g

/-- The continuum pullback of a smaller cylinder agrees exactly with first
pulling it to any larger finite marginal and then pulling that marginal to the
projective limit. -/
theorem projectiveLimitFiniteMarginalL2Pullback_compatible
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (hProjective : IsProjectiveMeasureFamily Q)
    {I J : Finset ι}
    (hJI : J ⊆ I)
    (f : Lp ℝ 2 (Q J)) :
    projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f =
      projectiveLimitFiniteMarginalL2Pullback μ Q hLimit I
        (projectiveFamilyFiniteMarginalL2Pullback Q hProjective hJI f) := by
  let hFinite :=
    projectiveFamilyRestrictionMeasurePreserving Q hProjective hJI
  let hLarge :=
    projectiveLimitRestrictionMeasurePreserving μ Q hLimit I
  have hRestrict :
      (J.restrict : (∀ i, α i) → (∀ i : J, α i)) =
        (Finset.restrict₂ hJI) ∘ I.restrict := by
    funext x
    rfl
  simpa [projectiveLimitFiniteMarginalL2Pullback,
    projectiveFamilyFiniteMarginalL2Pullback, hRestrict, hFinite, hLarge] using
    (Lp.compMeasurePreserving_comp_apply
      (E := ℝ) (p := (2 : ENNReal)) f hFinite hLarge)

/-- The finite-coordinate cylinder subspace inside the continuum `L²` carrier. -/
noncomputable def projectiveLimitFiniteMarginalL2CylinderSubspace
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (J : Finset ι) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  LinearMap.range
    (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).toLinearMap

/-- Cylinder subspaces are monotone under enlargement of the finite coordinate
set.  This is the directed-system statement needed for later density and
strong-limit constructions. -/
theorem projectiveLimitFiniteMarginalL2CylinderSubspace_mono
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (hProjective : IsProjectiveMeasureFamily Q)
    {I J : Finset ι}
    (hJI : J ⊆ I) :
    projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J ≤
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit I := by
  intro x hx
  rcases hx with ⟨f, rfl⟩
  refine ⟨projectiveFamilyFiniteMarginalL2Pullback Q hProjective hJI f, ?_⟩
  exact (projectiveLimitFiniteMarginalL2Pullback_compatible
    μ Q hLimit hProjective hJI f).symm

end

end MathlibAnalytic
end MGAP4D