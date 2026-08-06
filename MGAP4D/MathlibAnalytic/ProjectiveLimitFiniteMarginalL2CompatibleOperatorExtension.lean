import MGAP4D.MathlibAnalytic.ProjectiveLimitFiniteMarginalL2CylinderDensity
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Data.Set.UnionLift
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

section DirectedSubmoduleLift

variable
    {R M N ι : Type*}
    [Semiring R]
    [AddCommMonoid M]
    [Module R M]
    [AddCommMonoid N]
    [Module R N]
    [Nonempty ι]

/-- Glue a family of linear maps on a directed family of submodules when the
maps agree on every overlap. -/
noncomputable def directedSubmoduleISupLift
    (K : ι → Submodule R M)
    (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₗ[R] N)
    (hf : ∀ (i j : ι) (x : M)
      (hxi : x ∈ K i) (hxj : x ∈ K j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) :
    ↥(⨆ i, K i) →ₗ[R] N :=
  { toFun :=
      Set.iUnionLift (fun i => (K i : Set M)) (fun i x => f i x) hf
        (↑(⨆ i, K i) : Set M)
        (by rw [Submodule.coe_iSup_of_directed K dir])
    map_add' := by
      intro x y
      dsimp
      apply Set.iUnionLift_binary
        (Submodule.coe_iSup_of_directed K dir) dir _ (fun _ => (· + ·))
      all_goals simp
    map_smul' := fun r => by
      dsimp
      apply Set.iUnionLift_unary
        (Submodule.coe_iSup_of_directed K dir) _ (fun _ x => r • x)
        (fun _ _ => rfl)
      all_goals simp }

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem directedSubmoduleISupLift_inclusion
    {K : ι → Submodule R M}
    {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] N}
    {hf : ∀ (i j : ι) (x : M)
      (hxi : x ∈ K i) (hxj : x ∈ K j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
    {i : ι}
    (x : K i)
    (h : K i ≤ ⨆ j, K j) :
    directedSubmoduleISupLift K dir f hf (Submodule.inclusion h x) = f i x := by
  dsimp [directedSubmoduleISupLift]
  exact Set.iUnionLift_inclusion x h

set_option backward.isDefEq.respectTransparency false in
theorem directedSubmoduleISupLift_of_mem
    {K : ι → Submodule R M}
    {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] N}
    {hf : ∀ (i j : ι) (x : M)
      (hxi : x ∈ K i) (hxj : x ∈ K j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
    {i : ι}
    (x : ↥(⨆ j, K j))
    (hx : (x : M) ∈ K i) :
    directedSubmoduleISupLift K dir f hf x = f i ⟨x, hx⟩ := by
  dsimp [directedSubmoduleISupLift]
  exact Set.iUnionLift_of_mem x hx

end DirectedSubmoduleLift

variable
    {ι : Type*}
    {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]

/-- A uniformly bounded compatible family of bounded operators on all finite
marginal `L²` spaces of a projective system. Compatibility is exact under the
canonical finite-coordinate transition isometries. -/
structure ProjectiveLimitFiniteMarginalL2OperatorSystem
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (hProjective : IsProjectiveMeasureFamily Q) where
  localOperator :
    ∀ J : Finset ι,
      Lp ℝ 2 (Q J) →L[ℝ] Lp ℝ 2 (Q J)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  local_norm_le :
    ∀ (J : Finset ι) (f : Lp ℝ 2 (Q J)),
      ‖localOperator J f‖ ≤ bound * ‖f‖
  transition_intertwines :
    ∀ {I J : Finset ι} (hJI : J ⊆ I)
      (f : Lp ℝ 2 (Q J)),
      projectiveFamilyFiniteMarginalL2Pullback Q hProjective hJI
          (localOperator J f) =
        localOperator I
          (projectiveFamilyFiniteMarginalL2Pullback Q hProjective hJI f)

namespace ProjectiveLimitFiniteMarginalL2OperatorSystem

variable
    {μ : Measure (∀ i, α i)}
    {Q : ∀ J : Finset ι, Measure (∀ i : J, α i)}
    {hLimit : IsProjectiveLimit μ Q}
    {hProjective : IsProjectiveMeasureFamily Q}
    (S : ProjectiveLimitFiniteMarginalL2OperatorSystem
      μ Q hLimit hProjective)

/-- Conjugate one finite-marginal operator to its finite-coordinate cylinder
range inside the common continuum `L²` carrier, with values in the ambient
continuum space. -/
noncomputable def finiteCylinderOperator
    (J : Finset ι) :
    projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J →L[ℝ]
      Lp ℝ 2 μ := by
  let e := projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
  let eInv :
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J →L[ℝ]
        Lp ℝ 2 (Q J) :=
    (e.equivRange.symm.toContinuousLinearEquiv).toContinuousLinearMap
  exact e.toContinuousLinearMap.comp ((S.localOperator J).comp eInv)

@[simp] theorem finiteCylinderOperator_apply
    (J : Finset ι)
    (f : Lp ℝ 2 (Q J)) :
    S.finiteCylinderOperator J
        ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f) =
      projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (S.localOperator J f) := by
  let e := projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
  have hinv :
      (e.equivRange.symm.toContinuousLinearEquiv)
          (e.equivRange f) = f :=
    e.equivRange.symm_apply_apply f
  change e (S.localOperator J
    ((e.equivRange.symm.toContinuousLinearEquiv) (e.equivRange f))) =
      e (S.localOperator J f)
  rw [hinv]

/-- The uniform finite-marginal bound is unchanged after conjugation to a
continuum cylinder range. -/
theorem finiteCylinderOperator_norm_le
    (J : Finset ι)
    (x : projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J) :
    ‖S.finiteCylinderOperator J x‖ ≤ S.bound * ‖x‖ := by
  rcases
      (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange.surjective x
    with ⟨f, rfl⟩
  rw [S.finiteCylinderOperator_apply]
  calc
    ‖projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (S.localOperator J f)‖ = ‖S.localOperator J f‖ :=
      (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).norm_map _
    _ ≤ S.bound * ‖f‖ := S.local_norm_le J f
    _ = S.bound *
        ‖(projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f‖ := by
      rw [(projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange.norm_map]

/-- The finite-coordinate cylinder subspaces are a directed family: two finite
coordinate sets are dominated by their union. -/
theorem projectiveLimitFiniteMarginalL2CylinderSubspace_directed
    (hProjective : IsProjectiveMeasureFamily Q) :
    Directed (· ≤ ·)
      (fun J : Finset ι =>
        projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J) := by
  classical
  intro I J
  refine ⟨I ∪ J, ?_, ?_⟩
  · apply projectiveLimitFiniteMarginalL2CylinderSubspace_mono
      μ Q hLimit hProjective
    intro x hx
    simp [hx]
  · apply projectiveLimitFiniteMarginalL2CylinderSubspace_mono
      μ Q hLimit hProjective
    intro x hx
    simp [hx]

/-- Conjugated finite operators agree exactly under inclusion of nested
continuum cylinder ranges. -/
theorem finiteCylinderOperator_eq_comp_inclusion
    {I J : Finset ι}
    (hJI : J ⊆ I) :
    (S.finiteCylinderOperator J).toLinearMap =
      (S.finiteCylinderOperator I).toLinearMap.comp
        (Submodule.inclusion
          (projectiveLimitFiniteMarginalL2CylinderSubspace_mono
            μ Q hLimit hProjective hJI)) := by
  apply LinearMap.ext
  intro x
  rcases
      (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange.surjective x
    with ⟨f, rfl⟩
  have hInclusion :
      Submodule.inclusion
          (projectiveLimitFiniteMarginalL2CylinderSubspace_mono
            μ Q hLimit hProjective hJI)
          ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f) =
        (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit I).equivRange
          (projectiveFamilyFiniteMarginalL2Pullback
            Q hProjective hJI f) := by
    apply Subtype.ext
    exact projectiveLimitFiniteMarginalL2Pullback_compatible
      μ Q hLimit hProjective hJI f
  change
    S.finiteCylinderOperator J
        ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f) =
      S.finiteCylinderOperator I
        (Submodule.inclusion
          (projectiveLimitFiniteMarginalL2CylinderSubspace_mono
            μ Q hLimit hProjective hJI)
          ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f))
  rw [hInclusion, S.finiteCylinderOperator_apply,
    S.finiteCylinderOperator_apply]
  rw [← S.transition_intertwines hJI f]
  exact projectiveLimitFiniteMarginalL2Pullback_compatible
    μ Q hLimit hProjective hJI (S.localOperator J f)

/-- Conjugated finite operators agree on every overlap, even when neither
coordinate set is included in the other. -/
theorem finiteCylinderOperator_agree_on_overlap
    (I J : Finset ι)
    (x : Lp ℝ 2 μ)
    (hxI : x ∈ projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit I)
    (hxJ : x ∈ projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J) :
    S.finiteCylinderOperator I ⟨x, hxI⟩ =
      S.finiteCylinderOperator J ⟨x, hxJ⟩ := by
  classical
  let K := I ∪ J
  have hIK : I ⊆ K := by
    intro y hy
    simp [K, hy]
  have hJK : J ⊆ K := by
    intro y hy
    simp [K, hy]
  let hSubI := projectiveLimitFiniteMarginalL2CylinderSubspace_mono
    μ Q hLimit hProjective hIK
  let hSubJ := projectiveLimitFiniteMarginalL2CylinderSubspace_mono
    μ Q hLimit hProjective hJK
  have hEqI := congrArg
    (fun T :
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit I →ₗ[ℝ]
        Lp ℝ 2 μ => T ⟨x, hxI⟩)
    (S.finiteCylinderOperator_eq_comp_inclusion hIK)
  have hEqJ := congrArg
    (fun T :
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J →ₗ[ℝ]
        Lp ℝ 2 μ => T ⟨x, hxJ⟩)
    (S.finiteCylinderOperator_eq_comp_inclusion hJK)
  calc
    S.finiteCylinderOperator I ⟨x, hxI⟩ =
        S.finiteCylinderOperator K
          (Submodule.inclusion hSubI ⟨x, hxI⟩) := hEqI
    _ = S.finiteCylinderOperator K
          (Submodule.inclusion hSubJ ⟨x, hxJ⟩) :=
      congrArg (S.finiteCylinderOperator K) (Subtype.ext (by rfl))
    _ = S.finiteCylinderOperator J ⟨x, hxJ⟩ := hEqJ.symm

/-- The compatible finite operators glue to one linear operator on the algebraic
directed cylinder core. -/
noncomputable def cylinderCoreOperator :
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit →ₗ[ℝ]
      Lp ℝ 2 μ :=
  directedSubmoduleISupLift
    (fun J : Finset ι =>
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J)
    (projectiveLimitFiniteMarginalL2CylinderSubspace_directed
      (μ := μ) (Q := Q) (hLimit := hLimit) hProjective)
    (fun J => (S.finiteCylinderOperator J).toLinearMap)
    (fun I J x hxI hxJ =>
      S.finiteCylinderOperator_agree_on_overlap I J x hxI hxJ)

@[simp] theorem cylinderCoreOperator_apply_finite
    (J : Finset ι)
    (f : Lp ℝ 2 (Q J)) :
    S.cylinderCoreOperator
        (Submodule.inclusion
          (projectiveLimitFiniteMarginalL2CylinderSubspace_le_total
            μ Q hLimit J)
          ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f)) =
      projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (S.localOperator J f) := by
  change
    directedSubmoduleISupLift
        (fun K : Finset ι =>
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit K)
        (projectiveLimitFiniteMarginalL2CylinderSubspace_directed
          (μ := μ) (Q := Q) (hLimit := hLimit) hProjective)
        (fun K => (S.finiteCylinderOperator K).toLinearMap)
        (fun I K x hxI hxK =>
          S.finiteCylinderOperator_agree_on_overlap I K x hxI hxK)
        (Submodule.inclusion
          (projectiveLimitFiniteMarginalL2CylinderSubspace_le_total
            μ Q hLimit J)
          ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f)) = _
  calc
    _ = S.finiteCylinderOperator J
          ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f) :=
      directedSubmoduleISupLift_inclusion
        ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f)
        (projectiveLimitFiniteMarginalL2CylinderSubspace_le_total
          μ Q hLimit J)
    _ = _ := S.finiteCylinderOperator_apply J f

/-- Evaluate the glued cylinder-core operator using any finite cylinder range
that contains the given vector. -/
theorem cylinderCoreOperator_of_mem
    (x : projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit)
    (J : Finset ι)
    (hx : (x : Lp ℝ 2 μ) ∈
      projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J) :
    S.cylinderCoreOperator x =
      S.finiteCylinderOperator J ⟨x, hx⟩ := by
  change
    directedSubmoduleISupLift
        (fun K : Finset ι =>
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit K)
        (projectiveLimitFiniteMarginalL2CylinderSubspace_directed
          (μ := μ) (Q := Q) (hLimit := hLimit) hProjective)
        (fun K => (S.finiteCylinderOperator K).toLinearMap)
        (fun I K y hyI hyK =>
          S.finiteCylinderOperator_agree_on_overlap I K y hyI hyK) x = _
  exact directedSubmoduleISupLift_of_mem x hx

/-- The glued algebraic cylinder-core operator inherits the same uniform norm
bound as every finite marginal operator. -/
theorem cylinderCoreOperator_norm_le
    (x : projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit) :
    ‖S.cylinderCoreOperator x‖ ≤ S.bound * ‖x‖ := by
  have hxSup :
      (x : Lp ℝ 2 μ) ∈
        ⨆ J : Finset ι,
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J := by
    simpa [projectiveLimitFiniteMarginalL2CylinderTotalSubspace] using x.property
  rcases
      (Submodule.mem_iSup_of_directed
        (fun J : Finset ι =>
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J)
        (projectiveLimitFiniteMarginalL2CylinderSubspace_directed
          (μ := μ) (Q := Q) (hLimit := hLimit) hProjective)).1 hxSup
    with ⟨J, hxJ⟩
  rw [S.cylinderCoreOperator_of_mem x J hxJ]
  simpa using S.finiteCylinderOperator_norm_le J ⟨x, hxJ⟩

/-- The inclusion of the algebraic cylinder core into continuum `L²` has dense
range whenever the projective-limit measure is finite. -/
theorem cylinderCoreSubtype_denseRange
    [IsFiniteMeasure μ] :
    DenseRange
      (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).subtype := by
  simpa [DenseRange] using
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace_dense
      μ Q hLimit)

/-- The compatible uniformly bounded finite-marginal operator family has a
canonical bounded extension to the full continuum projective-limit `L²`
carrier. -/
noncomputable def continuumOperator
    [IsFiniteMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.cylinderCoreOperator.extendOfNorm
    (projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit).subtype

/-- The continuum extension agrees exactly with the glued operator on the dense
algebraic cylinder core. -/
theorem continuumOperator_apply_core
    [IsFiniteMeasure μ]
    (x : projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit) :
    S.continuumOperator (x : Lp ℝ 2 μ) = S.cylinderCoreOperator x := by
  simpa [continuumOperator] using
    (LinearMap.extendOfNorm_eq
      (f := S.cylinderCoreOperator)
      (e := (projectiveLimitFiniteMarginalL2CylinderTotalSubspace
        μ Q hLimit).subtype)
      (cylinderCoreSubtype_denseRange
        (μ := μ) (Q := Q) (hLimit := hLimit))
      ⟨S.bound, S.cylinderCoreOperator_norm_le⟩ x)

/-- Exact finite-to-continuum intertwining: applying the continuum operator to
a finite marginal cylinder is identical to applying the finite operator first
and then embedding. -/
theorem continuumOperator_intertwines_finite
    [IsFiniteMeasure μ]
    (J : Finset ι)
    (f : Lp ℝ 2 (Q J)) :
    S.continuumOperator
        (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f) =
      projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (S.localOperator J f) := by
  let x :=
    Submodule.inclusion
      (projectiveLimitFiniteMarginalL2CylinderSubspace_le_total
        μ Q hLimit J)
      ((projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f)
  have hxval :
      (x : Lp ℝ 2 μ) =
        projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f := rfl
  rw [← hxval, S.continuumOperator_apply_core x]
  exact S.cylinderCoreOperator_apply_finite J f

/-- The full continuum extension satisfies the same pointwise norm bound as the
finite marginal operators. -/
theorem continuumOperator_norm_le
    [IsFiniteMeasure μ]
    (x : Lp ℝ 2 μ) :
    ‖S.continuumOperator x‖ ≤ S.bound * ‖x‖ := by
  simpa [continuumOperator] using
    (LinearMap.norm_extendOfNorm_apply_le
      (f := S.cylinderCoreOperator)
      (e := (projectiveLimitFiniteMarginalL2CylinderTotalSubspace
        μ Q hLimit).subtype)
      (cylinderCoreSubtype_denseRange
        (μ := μ) (Q := Q) (hLimit := hLimit))
      S.bound S.cylinderCoreOperator_norm_le x)

/-- The operator norm of the continuum extension is bounded by the same common
finite-marginal constant. -/
theorem continuumOperator_opNorm_le
    [IsFiniteMeasure μ] :
    ‖S.continuumOperator‖ ≤ S.bound := by
  simpa [continuumOperator] using
    (LinearMap.opNorm_extendOfNorm_le
      (f := S.cylinderCoreOperator)
      (e := (projectiveLimitFiniteMarginalL2CylinderTotalSubspace
        μ Q hLimit).subtype)
      (cylinderCoreSubtype_denseRange
        (μ := μ) (Q := Q) (hLimit := hLimit))
      S.bound_nonneg S.cylinderCoreOperator_norm_le)

/-- Any bounded continuum operator satisfying all finite-marginal intertwining
equalities already agrees with the glued operator on the entire dense cylinder
core. -/
theorem toLinearMap_comp_coreSubtype_eq_of_intertwining
    (g : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hg : ∀ (J : Finset ι) (f : Lp ℝ 2 (Q J)),
      g (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f) =
        projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
          (S.localOperator J f)) :
    g.toLinearMap.comp
        (projectiveLimitFiniteMarginalL2CylinderTotalSubspace
          μ Q hLimit).subtype =
      S.cylinderCoreOperator := by
  apply LinearMap.ext
  intro x
  have hxSup :
      (x : Lp ℝ 2 μ) ∈
        ⨆ J : Finset ι,
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J := by
    simpa [projectiveLimitFiniteMarginalL2CylinderTotalSubspace] using x.property
  rcases
      (Submodule.mem_iSup_of_directed
        (fun J : Finset ι =>
          projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J)
        (projectiveLimitFiniteMarginalL2CylinderSubspace_directed
          (μ := μ) (Q := Q) (hLimit := hLimit) hProjective)).1 hxSup
    with ⟨J, hxJ⟩
  let xJ : projectiveLimitFiniteMarginalL2CylinderSubspace μ Q hLimit J :=
    ⟨x, hxJ⟩
  rcases
      (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange.surjective xJ
    with ⟨f, hf⟩
  have hval :
      projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f =
        (x : Lp ℝ 2 μ) :=
    congrArg Subtype.val hf
  change g (x : Lp ℝ 2 μ) = S.cylinderCoreOperator x
  rw [← hval, hg J f, S.cylinderCoreOperator_of_mem x J hxJ]
  have hxJ_eq :
      xJ =
        (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J).equivRange f :=
    hf.symm
  change
    projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
        (S.localOperator J f) =
      S.finiteCylinderOperator J xJ
  rw [hxJ_eq]
  exact (S.finiteCylinderOperator_apply J f).symm

/-- The canonical continuum extension is the unique bounded operator satisfying
all exact finite-marginal intertwining identities. -/
theorem continuumOperator_unique
    [IsFiniteMeasure μ]
    (g : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hg : ∀ (J : Finset ι) (f : Lp ℝ 2 (Q J)),
      g (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f) =
        projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
          (S.localOperator J f)) :
    S.continuumOperator = g := by
  simpa [continuumOperator] using
    (LinearMap.extendOfNorm_unique
      (f := S.cylinderCoreOperator)
      (e := (projectiveLimitFiniteMarginalL2CylinderTotalSubspace
        μ Q hLimit).subtype)
      (cylinderCoreSubtype_denseRange
        (μ := μ) (Q := Q) (hLimit := hLimit))
      S.bound S.cylinderCoreOperator_norm_le g
      (S.toLinearMap_comp_coreSubtype_eq_of_intertwining g hg))

end ProjectiveLimitFiniteMarginalL2OperatorSystem

/-- Audit-visible receipt for the complete compatible finite-operator extension
route from finite marginals to one continuum projective-limit `L²` carrier. -/
structure ProjectiveLimitFiniteMarginalL2OperatorExtensionPackage
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (hProjective : IsProjectiveMeasureFamily Q)
    [IsFiniteMeasure μ] where
  system :
    ProjectiveLimitFiniteMarginalL2OperatorSystem
      μ Q hLimit hProjective
  cylinderCoreOperator :
    projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit →ₗ[ℝ]
      Lp ℝ 2 μ
  continuumOperator :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
  coreAgreement :
    ∀ x : projectiveLimitFiniteMarginalL2CylinderTotalSubspace μ Q hLimit,
      continuumOperator (x : Lp ℝ 2 μ) = cylinderCoreOperator x
  finiteIntertwining :
    ∀ (J : Finset ι) (f : Lp ℝ 2 (Q J)),
      continuumOperator
          (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f) =
        projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
          (system.localOperator J f)
  continuumNormBound :
    ∀ x : Lp ℝ 2 μ,
      ‖continuumOperator x‖ ≤ system.bound * ‖x‖
  continuumOpNormBound :
    ‖continuumOperator‖ ≤ system.bound
  uniqueness :
    ∀ g : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ (J : Finset ι) (f : Lp ℝ 2 (Q J)),
        g (projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J f) =
          projectiveLimitFiniteMarginalL2Pullback μ Q hLimit J
            (system.localOperator J f)) →
      continuumOperator = g

/-- Construct the complete compatible finite-operator extension receipt. -/
noncomputable def projectiveLimitFiniteMarginalL2OperatorExtensionPackage
    (μ : Measure (∀ i, α i))
    (Q : ∀ J : Finset ι, Measure (∀ i : J, α i))
    (hLimit : IsProjectiveLimit μ Q)
    (hProjective : IsProjectiveMeasureFamily Q)
    [IsFiniteMeasure μ]
    (S : ProjectiveLimitFiniteMarginalL2OperatorSystem
      μ Q hLimit hProjective) :
    ProjectiveLimitFiniteMarginalL2OperatorExtensionPackage
      μ Q hLimit hProjective where
  system := S
  cylinderCoreOperator := S.cylinderCoreOperator
  continuumOperator := S.continuumOperator
  coreAgreement := S.continuumOperator_apply_core
  finiteIntertwining := S.continuumOperator_intertwines_finite
  continuumNormBound := S.continuumOperator_norm_le
  continuumOpNormBound := S.continuumOperator_opNorm_le
  uniqueness := S.continuumOperator_unique

end

end MathlibAnalytic
end MGAP4D
