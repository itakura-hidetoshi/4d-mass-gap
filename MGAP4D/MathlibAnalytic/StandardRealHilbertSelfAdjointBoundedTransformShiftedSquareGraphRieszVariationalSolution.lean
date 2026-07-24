import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformShiftedSquareVariationalSolutionSurjective
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- The graph of a partially defined real-Hilbert operator, transported to the `L²`
product.  Its inherited inner product is exactly

`⟪u,v⟫ + ⟪Au,Av⟫`.

Using the graph rather than installing a second norm directly on `A.domain` avoids
competing norm instances on the domain subtype. -/
def standardRealHilbertSelfAdjointGraphL2
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) :
    Submodule ℝ (WithLp 2 (H × H)) :=
  A.graph.comap
    (WithLp.prodContinuousLinearEquiv 2 ℝ H H).toLinearMap

/-- Self-adjointness makes the `L²` graph subspace closed. -/
theorem standardRealHilbertSelfAdjointGraphL2_isClosed
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {A : H →ₗ.[ℝ] H}
    (core : RealHilbertSelfAdjointCore A) :
    IsClosed
      ((standardRealHilbertSelfAdjointGraphL2 A :
          Submodule ℝ (WithLp 2 (H × H))) :
        Set (WithLp 2 (H × H))) := by
  change IsClosed
    ((WithLp.prodContinuousLinearEquiv 2 ℝ H H) ⁻¹'
      (A.graph : Set (H × H)))
  exact core.selfAdjoint.isClosed.preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ H H).continuous

/-- The ambient right-hand side `x` defines the bounded functional
`(v, Av) ↦ ⟪x,v⟫` on the `L²` graph Hilbert space. -/
def standardRealHilbertSelfAdjointGraphL2Functional
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H) (x : H) :
    StrongDual ℝ (standardRealHilbertSelfAdjointGraphL2 A) :=
  (innerSL ℝ x).comp
    ((WithLp.fstL 2 ℝ H H).comp
      (Submodule.subtypeL (standardRealHilbertSelfAdjointGraphL2 A)))

/-- The Riesz representative of the ambient functional on the closed graph Hilbert
space. -/
def standardRealHilbertSelfAdjointGraphL2RieszRepresentative
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    standardRealHilbertSelfAdjointGraphL2 A := by
  letI : CompleteSpace (standardRealHilbertSelfAdjointGraphL2 A) :=
    (standardRealHilbertSelfAdjointGraphL2_isClosed core).completeSpace_coe
  exact
    (InnerProductSpace.toDual ℝ
      (standardRealHilbertSelfAdjointGraphL2 A)).symm
        (standardRealHilbertSelfAdjointGraphL2Functional A x)

/-- The Riesz representative evaluates to the original ambient functional. -/
theorem standardRealHilbertSelfAdjointGraphL2RieszRepresentative_inner
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H)
    (v : standardRealHilbertSelfAdjointGraphL2 A) :
    inner ℝ
        (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x) v =
      inner ℝ x ((v : WithLp 2 (H × H)).fst) := by
  letI : CompleteSpace (standardRealHilbertSelfAdjointGraphL2 A) :=
    (standardRealHilbertSelfAdjointGraphL2_isClosed core).completeSpace_coe
  simpa [standardRealHilbertSelfAdjointGraphL2RieszRepresentative,
    standardRealHilbertSelfAdjointGraphL2Functional] using
      (InnerProductSpace.toDual_symm_apply
        (𝕜 := ℝ)
        (E := standardRealHilbertSelfAdjointGraphL2 A)
        (x := v)
        (y := standardRealHilbertSelfAdjointGraphL2Functional A x))

/-- A domain vector embedded as its graph point in the `L²` graph Hilbert space. -/
def standardRealHilbertSelfAdjointDomainToGraphL2
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →ₗ.[ℝ] H)
    (v : A.domain) :
    standardRealHilbertSelfAdjointGraphL2 A :=
  ⟨WithLp.toLp 2 ((v : H), A v), by
    change ((v : H), A v) ∈ A.graph
    exact A.mem_graph v⟩

/-- The Riesz representative is a genuine point of the original operator graph. -/
theorem standardRealHilbertSelfAdjointGraphL2RieszRepresentative_mem_graph
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    WithLp.ofLp
      (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x) ∈
        A.graph := by
  exact
    (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x).property

/-- Recover the domain component of the Riesz graph representative. -/
def standardRealHilbertSelfAdjointGraphRieszSolve
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    A.domain :=
  Classical.choose
    (A.mem_graph_iff'.mp
      (standardRealHilbertSelfAdjointGraphL2RieszRepresentative_mem_graph A core x))

/-- The recovered domain point and its image are exactly the two coordinates of the
Riesz graph representative. -/
theorem standardRealHilbertSelfAdjointGraphRieszSolve_graph_eq
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    ((standardRealHilbertSelfAdjointGraphRieszSolve A core x : H),
        A (standardRealHilbertSelfAdjointGraphRieszSolve A core x)) =
      WithLp.ofLp
        (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x) := by
  exact
    Classical.choose_spec
      (A.mem_graph_iff'.mp
        (standardRealHilbertSelfAdjointGraphL2RieszRepresentative_mem_graph A core x))

/-- First-coordinate identification for the recovered domain point. -/
theorem standardRealHilbertSelfAdjointGraphRieszSolve_coe
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    (standardRealHilbertSelfAdjointGraphRieszSolve A core x : H) =
      (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x :
        WithLp 2 (H × H)).fst := by
  have h := congrArg Prod.fst
    (standardRealHilbertSelfAdjointGraphRieszSolve_graph_eq A core x)
  simpa using h

/-- Second-coordinate identification for the recovered operator image. -/
theorem standardRealHilbertSelfAdjointGraphRieszSolve_image
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H) :
    A (standardRealHilbertSelfAdjointGraphRieszSolve A core x) =
      (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x :
        WithLp 2 (H × H)).snd := by
  have h := congrArg Prod.snd
    (standardRealHilbertSelfAdjointGraphRieszSolve_graph_eq A core x)
  simpa using h

/-- Riesz representation on the closed graph produces the required weak graph-form
solution for every ambient right-hand side. -/
theorem standardRealHilbertSelfAdjointGraphRieszSolve_variational_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A)
    (x : H)
    (v : A.domain) :
    inner ℝ
        (standardRealHilbertSelfAdjointGraphRieszSolve A core x : H)
        (v : H) +
      inner ℝ
        (A (standardRealHilbertSelfAdjointGraphRieszSolve A core x))
        (A v) =
      inner ℝ x (v : H) := by
  have h :=
    standardRealHilbertSelfAdjointGraphL2RieszRepresentative_inner
      A core x (standardRealHilbertSelfAdjointDomainToGraphL2 A v)
  change
    inner ℝ
        (standardRealHilbertSelfAdjointGraphL2RieszRepresentative A core x :
          WithLp 2 (H × H))
        (standardRealHilbertSelfAdjointDomainToGraphL2 A v :
          WithLp 2 (H × H)) =
      inner ℝ x
        ((standardRealHilbertSelfAdjointDomainToGraphL2 A v :
          WithLp 2 (H × H)).fst) at h
  rw [WithLp.prod_inner_apply] at h
  simp only [standardRealHilbertSelfAdjointDomainToGraphL2,
    WithLp.toLp_fst, WithLp.toLp_snd] at h
  rw [← standardRealHilbertSelfAdjointGraphRieszSolve_coe A core x,
    ← standardRealHilbertSelfAdjointGraphRieszSolve_image A core x] at h
  exact h

/-- The graph-space Riesz construction discharges the sole independent weak-solution
boundary used by the shifted-square surjectivity route. -/
def standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataOfGraphRiesz
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionData A where
  solve := standardRealHilbertSelfAdjointGraphRieszSolve A core
  variational_identity :=
    standardRealHilbertSelfAdjointGraphRieszSolve_variational_identity A core

/-- Uniform graph-space Riesz constructor for weak shifted-square solutions. -/
def standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareGraphRieszVariationalSolutionDataConstructor :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataConstructor where
  construct := fun A core =>
    standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareVariationalSolutionDataOfGraphRiesz
      A core

/-- Consequently shifted-square surjectivity no longer needs an independent
constructor: it is generated uniformly from self-adjointness by graph-space Riesz
representation. -/
def standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareGraphRieszSurjectiveDataConstructor :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareSurjectiveDataConstructor :=
  standardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareGraphRieszVariationalSolutionDataConstructor.toSurjectiveDataConstructor

end

end MathlibAnalytic
end MGAP4D
