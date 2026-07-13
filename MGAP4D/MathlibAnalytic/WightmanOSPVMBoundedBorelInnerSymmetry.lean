import MGAP4D.MathlibAnalytic.WightmanOSPVMPositiveSpectralSupportDerived
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped BigOperators InnerProductSpace

noncomputable section

/-- A finite real PVM spectral integral is symmetric for the real Hilbert inner
product. -/
theorem pvmFiniteSimpleSpectralIntegralOperator_inner_eq
    {H ι : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι]
    (P : OrthogonalProjectionValuedSetFunction H)
    (coefficients : ι → ℝ) (carrier : ι → Set ℝ)
    (x y : H) :
    inner ℝ
        (pvmFiniteSimpleSpectralIntegralOperator P coefficients carrier x) y =
      inner ℝ x
        (pvmFiniteSimpleSpectralIntegralOperator P coefficients carrier y) := by
  simp only [pvmFiniteSimpleSpectralIntegralOperator_apply,
    pvmFiniteSimpleSpectralIntegral, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [P.selfAdjoint]

/-- Canonical simple-function PVM integration is inner-product symmetric. -/
theorem pvmSimpleFuncSpectralIntegralOperator_inner_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : MeasureTheory.SimpleFunc ℝ ℝ)
    (x y : H) :
    inner ℝ (pvmSimpleFuncSpectralIntegralOperator P f x) y =
      inner ℝ x (pvmSimpleFuncSpectralIntegralOperator P f y) := by
  exact pvmFiniteSimpleSpectralIntegralOperator_inner_eq
    P (fun c : f.range => (c : ℝ)) (pvmSimpleFuncFiber f) x y

/-- Operator-norm completion preserves the inner symmetry of every real bounded
Borel PVM spectral integral. -/
theorem pvmBoundedBorelSpectralIntegralOperator_inner_eq
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F : PVMBoundedBorelRealFunction)
    (x y : H) :
    inner ℝ (pvmBoundedBorelSpectralIntegralOperator P F x) y =
      inner ℝ x (pvmBoundedBorelSpectralIntegralOperator P F y) := by
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  have hx := A.tendsto_completedOperator_apply P x
  have hy := A.tendsto_completedOperator_apply P y
  have hLeft :
      Tendsto
        (fun n : ℕ =>
          inner ℝ (pvmSimpleFuncSpectralIntegralOperator P (A.simple n) x) y)
        atTop
        (𝓝 (inner ℝ (A.completedOperator P x) y)) :=
    hx.inner tendsto_const_nhds
  have hRight :
      Tendsto
        (fun n : ℕ =>
          inner ℝ x (pvmSimpleFuncSpectralIntegralOperator P (A.simple n) y))
        atTop
        (𝓝 (inner ℝ x (A.completedOperator P y))) :=
    tendsto_const_nhds.inner hy
  have hFunctions :
      (fun n : ℕ =>
        inner ℝ (pvmSimpleFuncSpectralIntegralOperator P (A.simple n) x) y) =
      (fun n : ℕ =>
        inner ℝ x (pvmSimpleFuncSpectralIntegralOperator P (A.simple n) y)) := by
    funext n
    exact pvmSimpleFuncSpectralIntegralOperator_inner_eq
      P (A.simple n) x y
  rw [hFunctions] at hLeft
  have hCompleted :
      inner ℝ (A.completedOperator P x) y =
        inner ℝ x (A.completedOperator P y) :=
    tendsto_nhds_unique hLeft hRight
  simpa [A, pvmBoundedBorelSpectralIntegralOperator] using hCompleted

/-- On a real Hilbert space, two symmetric bounded operators are equal as soon as
their quadratic forms agree on every vector. -/
theorem continuousLinearMap_eq_of_inner_self_eq_of_innerSymmetric
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T U : H →L[ℝ] H)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y))
    (hU : ∀ x y : H, inner ℝ (U x) y = inner ℝ x (U y))
    (hQuadratic : ∀ x : H, inner ℝ x (T x) = inner ℝ x (U x)) :
    T = U := by
  have hCross : ∀ x y : H, inner ℝ x (T y) = inner ℝ x (U y) := by
    intro x y
    have hxy := hQuadratic (x + y)
    have hx := hQuadratic x
    have hy := hQuadratic y
    simp only [map_add, inner_add_left, inner_add_right] at hxy
    rw [← hT y x, ← hU y x] at hxy
    have hTyx : inner ℝ (T y) x = inner ℝ x (T y) := by
      exact (real_inner_comm (T y) x).symm
    have hUyx : inner ℝ (U y) x = inner ℝ x (U y) := by
      exact (real_inner_comm (U y) x).symm
    rw [hTyx, hUyx] at hxy
    nlinarith
  ext x
  let z : H := T x - U x
  have hz : inner ℝ z z = 0 := by
    dsimp [z]
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (hCross z x)
  have hnorm : ‖z‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hz
  have hzZero : z = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  exact sub_eq_zero.mp hzZero

end

end MathlibAnalytic
end MGAP4D
