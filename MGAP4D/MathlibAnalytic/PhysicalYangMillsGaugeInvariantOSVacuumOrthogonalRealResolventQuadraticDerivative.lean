import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventPositive
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The continuous real resolvent is injective.  It is the ambient realization
of the inverse shifted-domain equivalence. -/
theorem realResolvent_injective
    (A : E →ₗ.[ℝ] E) {mass lambda : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hlambda : lambda < mass)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Function.Injective (A.realResolvent hSelf hlambda hgap) := by
  intro y z hyz
  let e := A.realShiftLinearEquiv hSelf hlambda hgap
  apply e.symm.injective
  apply Subtype.ext
  simpa only [realResolvent_apply, e] using hyz

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 1200000

/-- Applying the operator-valued derivative formula to a fixed excitation vector
gives the vector-valued resolvent derivative. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventOn_apply_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    HasDerivAt
      (fun mu => G.vacuumOrthogonalRealResolventOn T hP hSelf mu y)
      (((G.vacuumOrthogonalRealResolvent T hP hSelf hlambda).comp
        (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda)) y)
      lambda := by
  have hoperator :=
    G.vacuumOrthogonalRealResolventOn_hasDerivAt T hP hSelf hlambda
  have hconstant : HasDerivAt (fun _ : ℝ => y) 0 lambda :=
    hasDerivAt_const lambda y
  simpa using hoperator.clm_apply hconstant

/-- The scalar quadratic resolvent function associated with an excitation
vector. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    (lambda : ℝ) : ℝ :=
  inner ℝ (G.vacuumOrthogonalRealResolventOn T hP hSelf lambda y) y

/-- The derivative of the scalar quadratic resolvent is the squared norm of the
resolved excitation. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    HasDerivAt
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y‖ ^ 2
      lambda := by
  let R := G.vacuumOrthogonalRealResolvent T hP hSelf hlambda
  have hvector :=
    G.vacuumOrthogonalRealResolventOn_apply_hasDerivAt
      T hP hSelf hlambda y
  have hinner := hvector.inner ℝ (hasDerivAt_const lambda y)
  have hderivative :
      inner ℝ ((R.comp R) y) y = ‖R y‖ ^ 2 := by
    calc
      inner ℝ ((R.comp R) y) y = inner ℝ (R (R y)) y := rfl
      _ = inner ℝ (R y) (R y) :=
        G.vacuumOrthogonalRealResolvent_symmetric
          T hP hSelf hlambda (R y) y
      _ = ‖R y‖ ^ 2 := real_inner_self_eq_norm_sq
  simpa only [vacuumOrthogonalRealResolventQuadraticOn,
    inner_zero_right, zero_add, R, hderivative] using hinner

/-- Exact derivative formula for the scalar quadratic resolvent. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_deriv
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    deriv (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y) lambda =
      ‖G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y‖ ^ 2 :=
  (G.vacuumOrthogonalRealResolventQuadraticOn_hasDerivAt
    T hP hSelf hlambda y).deriv

/-- The scalar quadratic resolvent derivative is nonnegative throughout the
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_deriv_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    (y : P.VacuumOrthogonalHilbert) :
    0 ≤ deriv
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y) lambda := by
  rw [G.vacuumOrthogonalRealResolventQuadraticOn_deriv
    T hP hSelf hlambda y]
  positivity

/-- For a nonzero excitation vector, the scalar quadratic resolvent derivative
is strictly positive. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_deriv_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ} (hlambda : lambda < G.mass)
    {y : P.VacuumOrthogonalHilbert} (hy : y ≠ 0) :
    0 < deriv
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y) lambda := by
  rw [G.vacuumOrthogonalRealResolventQuadraticOn_deriv
    T hP hSelf hlambda y]
  have hInjective : Function.Injective
      (G.vacuumOrthogonalRealResolvent T hP hSelf hlambda) := by
    apply LinearPMap.realResolvent_injective
      (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
      (hSelf :=
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
          hP hSelf)
      hlambda
    intro x
    simpa only [vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
      G.vacuumOrthogonalClosedRightHamiltonian_gap T hP
        ((T.closedRightHamiltonian_selfAdjoint_iff_isFormalAdjoint).mp hSelf) x
  have hresolved :
      G.vacuumOrthogonalRealResolvent T hP hSelf hlambda y ≠ 0 := by
    intro hzero
    apply hy
    apply hInjective
    simpa using hzero
  exact sq_pos_of_pos (norm_pos_iff.mpr hresolved)

/-- For each excitation vector, the positive quadratic resolvent is monotone in
the real spectral parameter below the transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_monotoneOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert) :
    MonotoneOn
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) := by
  apply monotoneOn_of_deriv_nonneg convex_Iio
  · intro lambda hlambda
    exact (G.vacuumOrthogonalRealResolventQuadraticOn_hasDerivAt
      T hP hSelf hlambda y).continuousAt.continuousWithinAt
  · intro lambda hlambda
    have hlambda' : lambda < G.mass := by simpa using hlambda
    exact (G.vacuumOrthogonalRealResolventQuadraticOn_hasDerivAt
      T hP hSelf hlambda' y).differentiableAt.differentiableWithinAt
  · intro lambda hlambda
    have hlambda' : lambda < G.mass := by simpa using hlambda
    exact G.vacuumOrthogonalRealResolventQuadraticOn_deriv_nonneg
      T hP hSelf hlambda' y

/-- For a nonzero excitation vector, the scalar quadratic resolvent is strictly
increasing throughout the real sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_strictMonoOn
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {y : P.VacuumOrthogonalHilbert} (hy : y ≠ 0) :
    StrictMonoOn
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) := by
  apply strictMonoOn_of_deriv_pos convex_Iio
  · intro lambda hlambda
    exact (G.vacuumOrthogonalRealResolventQuadraticOn_hasDerivAt
      T hP hSelf hlambda y).continuousAt.continuousWithinAt
  · intro lambda hlambda
    have hlambda' : lambda < G.mass := by simpa using hlambda
    exact G.vacuumOrthogonalRealResolventQuadraticOn_deriv_pos
      T hP hSelf hlambda' hy

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
