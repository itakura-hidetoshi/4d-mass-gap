import MGAP4D.MathlibAnalytic.WightmanOSPVMFiniteSimpleSpectralIntegral
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The canonical spectral carrier belonging to one value in the finite range of
`f`. -/
def pvmSimpleFuncFiber
    (f : SimpleFunc ℝ ℝ) (c : f.range) : Set ℝ :=
  f ⁻¹' ({(c : ℝ)} : Set ℝ)

/-- Canonical simple-function fibers are measurable. -/
theorem pvmSimpleFuncFiber_measurable
    (f : SimpleFunc ℝ ℝ) (c : f.range) :
    MeasurableSet (pvmSimpleFuncFiber f c) := by
  exact f.measurableSet_fiber (c : ℝ)

/-- Distinct values of a simple function have disjoint canonical fibers. -/
theorem pvmSimpleFuncFiber_pairwise_disjoint
    (f : SimpleFunc ℝ ℝ) :
    Pairwise (Function.onFun Disjoint (pvmSimpleFuncFiber f)) := by
  intro a b hab
  change Disjoint (pvmSimpleFuncFiber f a) (pvmSimpleFuncFiber f b)
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hfa : f x = (a : ℝ) := by
    simpa [pvmSimpleFuncFiber] using hxa
  have hfb : f x = (b : ℝ) := by
    simpa [pvmSimpleFuncFiber] using hxb
  apply hab
  apply Subtype.ext
  exact hfa.symm.trans hfb

/-- The canonical fibers of a simple function cover the whole spectral line. -/
theorem pvmSimpleFuncFiber_iUnion_eq_univ
    (f : SimpleFunc ℝ ℝ) :
    (⋃ c : f.range, pvmSimpleFuncFiber f c) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rw [Set.mem_iUnion]
    refine ⟨⟨f x, SimpleFunc.mem_range_self f x⟩, ?_⟩
    simp [pvmSimpleFuncFiber]

/-- The canonical PVM spectral integral of a Mathlib simple real function.

The finite range itself is used as the indexing type, so no external presentation
of the simple function is retained. -/
def pvmSimpleFuncSpectralIntegralOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ) : H →L[ℝ] H :=
  pvmFiniteSimpleSpectralIntegralOperator P
    (fun c : f.range => (c : ℝ))
    (pvmSimpleFuncFiber f)

@[simp] theorem pvmSimpleFuncSpectralIntegralOperator_apply
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ) (x : H) :
    pvmSimpleFuncSpectralIntegralOperator P f x =
      pvmFiniteSimpleSpectralIntegral P
        (fun c : f.range => (c : ℝ))
        (pvmSimpleFuncFiber f) x := by
  exact pvmFiniteSimpleSpectralIntegralOperator_apply
    P (fun c : f.range => (c : ℝ)) (pvmSimpleFuncFiber f) x

/-- A pointwise bound on a simple function bounds every coefficient in its
canonical finite-range presentation. -/
theorem pvmSimpleFunc_range_abs_le
    (f : SimpleFunc ℝ ℝ) (C : ℝ)
    (hBound : ∀ t : ℝ, ‖f t‖ ≤ C)
    (c : f.range) : |(c : ℝ)| ≤ C := by
  rcases SimpleFunc.mem_range.mp c.property with ⟨t, ht⟩
  simpa [Real.norm_eq_abs, ht] using hBound t

/-- The canonical simple-function spectral integral has the sharp pointwise
supremum-norm estimate. -/
theorem pvmSimpleFuncSpectralIntegralOperator_norm_le
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ t : ℝ, ‖f t‖ ≤ C)
    (x : H) :
    ‖pvmSimpleFuncSpectralIntegralOperator P f x‖ ≤ C * ‖x‖ := by
  rw [pvmSimpleFuncSpectralIntegralOperator_apply]
  exact pvmFiniteSimpleSpectralIntegral_norm_le
    P (fun c : f.range => (c : ℝ)) (pvmSimpleFuncFiber f)
      (pvmSimpleFuncFiber_pairwise_disjoint f)
      (pvmSimpleFuncFiber_iUnion_eq_univ f)
      C hC (pvmSimpleFunc_range_abs_le f C hBound) x

/-- Operator-norm form of the canonical simple-function contraction estimate. -/
theorem pvmSimpleFuncSpectralIntegralOperator_opNorm_le
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ t : ℝ, ‖f t‖ ≤ C) :
    ‖pvmSimpleFuncSpectralIntegralOperator P f‖ ≤ C := by
  exact pvmFiniteSimpleSpectralIntegralOperator_opNorm_le
    P (fun c : f.range => (c : ℝ)) (pvmSimpleFuncFiber f)
      (pvmSimpleFuncFiber_pairwise_disjoint f)
      (pvmSimpleFuncFiber_iUnion_eq_univ f)
      C hC (pvmSimpleFunc_range_abs_le f C hBound)

/-- Every canonical simple-function spectral integral therefore has an explicit
finite operator-norm bound. -/
theorem pvmSimpleFuncSpectralIntegralOperator_exists_opNorm_bound
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : SimpleFunc ℝ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖pvmSimpleFuncSpectralIntegralOperator P f‖ ≤ C := by
  obtain ⟨C, hC⟩ := (f.map fun x : ℝ => ‖x‖).exists_forall_le
  have hBound : ∀ t : ℝ, ‖f t‖ ≤ C := by
    intro t
    simpa [SimpleFunc.map_apply] using hC t
  have hC0 : 0 ≤ C :=
    (norm_nonneg (f 0)).trans (hBound 0)
  exact ⟨C, hC0,
    pvmSimpleFuncSpectralIntegralOperator_opNorm_le P f C hC0 hBound⟩

/-- A Cauchy family of canonical simple-function spectral integrals.  Completeness
of the continuous-operator space constructs its bounded operator limit. -/
structure PVMSimpleFuncOperatorCauchyApproximation
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H) where
  simple : ℕ → SimpleFunc ℝ ℝ
  operator_cauchy :
    CauchySeq (fun n => pvmSimpleFuncSpectralIntegralOperator P (simple n))

/-- The bounded operator obtained by completing a Cauchy sequence of canonical
simple-function spectral integrals. -/
noncomputable def PVMSimpleFuncOperatorCauchyApproximation.completedOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : OrthogonalProjectionValuedSetFunction H}
    (A : PVMSimpleFuncOperatorCauchyApproximation P) : H →L[ℝ] H :=
  Classical.choose (cauchySeq_tendsto_of_complete A.operator_cauchy)

/-- The canonical simple-function operators converge in operator norm to the
completed operator. -/
theorem PVMSimpleFuncOperatorCauchyApproximation.tendsto_completedOperator
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : OrthogonalProjectionValuedSetFunction H}
    (A : PVMSimpleFuncOperatorCauchyApproximation P) :
    Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
      atTop (𝓝 A.completedOperator) := by
  exact Classical.choose_spec
    (cauchySeq_tendsto_of_complete A.operator_cauchy)

/-- The completed operator is the unique operator-norm limit of its canonical
simple-function approximants. -/
theorem PVMSimpleFuncOperatorCauchyApproximation.completedOperator_eq_of_tendsto
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : OrthogonalProjectionValuedSetFunction H}
    (A : PVMSimpleFuncOperatorCauchyApproximation P)
    (T : H →L[ℝ] H)
    (hT : Tendsto
      (fun n => pvmSimpleFuncSpectralIntegralOperator P (A.simple n))
      atTop (𝓝 T)) :
    A.completedOperator = T := by
  exact tendsto_nhds_unique A.tendsto_completedOperator hT

/-- Two Cauchy approximation packages with termwise identical canonical
simple-function operators have the same completed operator. -/
theorem pvmSimpleFunc_completedOperator_eq_of_termwise_operator_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : OrthogonalProjectionValuedSetFunction H}
    (A B : PVMSimpleFuncOperatorCauchyApproximation P)
    (h : ∀ n : ℕ,
      pvmSimpleFuncSpectralIntegralOperator P (A.simple n) =
        pvmSimpleFuncSpectralIntegralOperator P (B.simple n)) :
    A.completedOperator = B.completedOperator := by
  apply A.completedOperator_eq_of_tendsto
  simpa only [h] using B.tendsto_completedOperator

end

end MathlibAnalytic
end MGAP4D
