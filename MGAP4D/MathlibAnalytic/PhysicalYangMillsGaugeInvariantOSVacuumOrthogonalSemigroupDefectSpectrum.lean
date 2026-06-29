import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingVacuumOrthogonalSemigroup
import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitSpectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PhysicalSemigroup

/-- A symmetric vacuum-fixing physical semigroup restricted to the complete
vacuum-orthogonal excitation Hilbert space. -/
noncomputable def vacuumOrthogonalOperator
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ((T.operator t).comp P.vacuumOrthogonal.subtypeL).codRestrict
    P.vacuumOrthogonal
    (fun x =>
      T.operator_mem_vacuumOrthogonal hSymmetric t
        (x : P.PhysicalHilbert) x.property)

@[simp] theorem vacuumOrthogonalOperator_apply
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal)
    (x : P.VacuumOrthogonalHilbert) :
    ((T.vacuumOrthogonalOperator hSymmetric t x :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
      T.operator t (x : P.PhysicalHilbert) := by
  rfl

/-- The restricted physical semigroup remains symmetric on the excitation
sector. -/
theorem vacuumOrthogonalOperator_inner_symm
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal)
    (x y : P.VacuumOrthogonalHilbert) :
    inner ℝ (T.vacuumOrthogonalOperator hSymmetric t x) y =
      inner ℝ x (T.vacuumOrthogonalOperator hSymmetric t y) := by
  change
    inner ℝ
        (T.operator t (x : P.PhysicalHilbert))
        (y : P.PhysicalHilbert) =
      inner ℝ
        (x : P.PhysicalHilbert)
        (T.operator t (y : P.PhysicalHilbert))
  exact hSymmetric t (x : P.PhysicalHilbert) (y : P.PhysicalHilbert)

/-- The bounded positive-time excitation defect `I - T(t)`. -/
noncomputable def vacuumOrthogonalDefect
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.id ℝ P.VacuumOrthogonalHilbert -
    T.vacuumOrthogonalOperator hSymmetric t

@[simp] theorem vacuumOrthogonalDefect_apply
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal)
    (x : P.VacuumOrthogonalHilbert) :
    T.vacuumOrthogonalDefect hSymmetric t x =
      x - T.vacuumOrthogonalOperator hSymmetric t x := by
  rfl

/-- The positive-time excitation defect is symmetric. -/
theorem vacuumOrthogonalDefect_symmetric
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) :
    ((T.vacuumOrthogonalDefect hSymmetric t :
        P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert) :
      P.VacuumOrthogonalHilbert →ₗ[ℝ] P.VacuumOrthogonalHilbert).IsSymmetric := by
  intro x y
  rw [vacuumOrthogonalDefect_apply, vacuumOrthogonalDefect_apply,
    inner_sub_left, inner_sub_right]
  exact congrArg
    (fun z : ℝ => inner ℝ x y - z)
    (T.vacuumOrthogonalOperator_inner_symm hSymmetric t x y)

end PhysicalSemigroup

namespace StronglyContinuousPhysicalSemigroup

/-- A continuum semigroup decay estimate gives a coercive lower bound for the
bounded positive-time defect on the excitation Hilbert space. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalDefect_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (x : P.VacuumOrthogonalHilbert) :
    (1 - G.decayFactor t) * ‖x‖ ^ 2 ≤
      inner ℝ
        (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t x)
        x := by
  have hxOrthogonal :
      inner ℝ (x : P.PhysicalHilbert) P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff (x : P.PhysicalHilbert)).mp x.property
  have hDecay := G.decay t (x : P.PhysicalHilbert) hxOrthogonal
  have hInner :
      inner ℝ
          (T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert))
          (x : P.PhysicalHilbert) ≤
        G.decayFactor t * ‖x‖ ^ 2 := by
    calc
      inner ℝ
          (T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert))
          (x : P.PhysicalHilbert) ≤
          ‖T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert)‖ * ‖x‖ :=
        real_inner_le_norm _ _
      _ ≤ (G.decayFactor t * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hDecay (norm_nonneg x)
      _ = G.decayFactor t * ‖x‖ ^ 2 := by ring
  rw [PhysicalSemigroup.vacuumOrthogonalDefect_apply]
  change
    (1 - G.decayFactor t) * ‖x‖ ^ 2 ≤
      inner ℝ
        ((x : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert))
        (x : P.PhysicalHilbert)
  calc
    (1 - G.decayFactor t) * ‖x‖ ^ 2 =
        ‖x‖ ^ 2 - G.decayFactor t * ‖x‖ ^ 2 := by ring
    _ ≤ ‖x‖ ^ 2 -
        inner ℝ
          (T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert))
          (x : P.PhysicalHilbert) :=
      sub_le_sub_left hInner _
    _ = inner ℝ
        ((x : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator t (x : P.PhysicalHilbert))
        (x : P.PhysicalHilbert) := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]

/-- At every time where the vacuum-sector contraction factor is strictly below
one, the bounded excitation defect supplies a positive coercive symmetric
operator package. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalDefectStrongLimitData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData
      Unit P.VacuumOrthogonalHilbert (Filter.pure ()) :=
  { approximant := fun _ =>
      T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t
    limitOperator :=
      T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t
    gap := 1 - G.decayFactor t
    gap_pos := sub_pos.mpr ht
    approximant_gap := fun _ x =>
      G.vacuumOrthogonalDefect_gap T hSymmetric t x
    strong_tendsto := fun _ => tendsto_const_nhds
    approximant_symmetric := fun _ =>
      T.toPhysicalSemigroup.vacuumOrthogonalDefect_symmetric hSymmetric t }

/-- The real algebra spectrum of the positive-time excitation defect is bounded
below by the finite-volume transferred contraction deficit. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalDefect_spectrum_subset_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1) :
    spectrum ℝ
        (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
      Set.Ici (1 - G.decayFactor t) :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_spectrum_subset_Ici
    (G.vacuumOrthogonalDefectStrongLimitData T hSymmetric t ht)

/-- Every real parameter below the positive-time contraction deficit belongs to
the resolvent set of the excitation defect. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalDefect_mem_resolventSet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1)
    {lambda : ℝ}
    (hlambda : lambda < 1 - G.decayFactor t) :
    lambda ∈ resolventSet ℝ
      (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
    (G.vacuumOrthogonalDefectStrongLimitData T hSymmetric t ht)
    hlambda

/-- The excitation-defect resolvent satisfies the inverse-distance norm bound. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalDefect_resolvent_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1)
    {lambda : ℝ}
    (hlambda : lambda < 1 - G.decayFactor t) :
    ‖(G.vacuumOrthogonalDefectStrongLimitData T hSymmetric t ht).limitResolvent
        hlambda‖ ≤
      (1 - G.decayFactor t - lambda)⁻¹ :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
    (G.vacuumOrthogonalDefectStrongLimitData T hSymmetric t ht)
    hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
