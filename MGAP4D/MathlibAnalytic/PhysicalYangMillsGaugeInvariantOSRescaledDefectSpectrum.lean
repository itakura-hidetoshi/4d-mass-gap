import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSmallTimeDefectSpectrum

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

/-- The bounded excitation-sector difference quotient
`t⁻¹ (I - T(t))` at positive Euclidean time. -/
noncomputable def vacuumOrthogonalRescaledDefect
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  (t : ℝ)⁻¹ • T.vacuumOrthogonalDefect hSymmetric t

@[simp] theorem vacuumOrthogonalRescaledDefect_apply
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal)
    (x : P.VacuumOrthogonalHilbert) :
    T.vacuumOrthogonalRescaledDefect hSymmetric t x =
      (t : ℝ)⁻¹ •
        T.vacuumOrthogonalDefect hSymmetric t x := by
  rfl

/-- The excitation-sector difference quotient remains symmetric. -/
theorem vacuumOrthogonalRescaledDefect_symmetric
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) :
    ((T.vacuumOrthogonalRescaledDefect hSymmetric t :
        P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert) :
      P.VacuumOrthogonalHilbert →ₗ[ℝ] P.VacuumOrthogonalHilbert).IsSymmetric := by
  intro x y
  change
    inner ℝ
        ((t : ℝ)⁻¹ •
          T.vacuumOrthogonalDefect hSymmetric t x) y =
      inner ℝ x
        ((t : ℝ)⁻¹ •
          T.vacuumOrthogonalDefect hSymmetric t y)
  rw [real_inner_smul_left, real_inner_smul_right]
  exact congrArg
    (fun z : ℝ => (t : ℝ)⁻¹ * z)
    (T.vacuumOrthogonalDefect_symmetric hSymmetric t x y)

end PhysicalSemigroup

namespace StronglyContinuousPhysicalSemigroup

/-- A linear lower bound for `1 - decayFactor(t)` becomes the time-independent
quadratic lower bound `mass / 2` for the rescaled excitation defect. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalRescaledDefect_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : 0 < t)
    (hLinear : (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t)
    (x : P.VacuumOrthogonalHilbert) :
    (G.mass / 2) * ‖x‖ ^ 2 ≤
      inner ℝ
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hSymmetric t x)
        x := by
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have hSlopeLowerDiv :
      G.mass / 2 ≤ (1 - G.decayFactor t) / (t : ℝ) :=
    (le_div_iff₀ htReal).2 hLinear
  have hSlopeLower :
      G.mass / 2 ≤ (t : ℝ)⁻¹ * (1 - G.decayFactor t) := by
    simpa [inv_mul_eq_div] using hSlopeLowerDiv
  have hDefect := G.vacuumOrthogonalDefect_gap T hSymmetric t x
  have hScaledDefect :
      (t : ℝ)⁻¹ * ((1 - G.decayFactor t) * ‖x‖ ^ 2) ≤
        (t : ℝ)⁻¹ *
          inner ℝ
            (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t x)
            x :=
    mul_le_mul_of_nonneg_left hDefect (inv_nonneg.mpr htReal.le)
  calc
    (G.mass / 2) * ‖x‖ ^ 2 ≤
        ((t : ℝ)⁻¹ * (1 - G.decayFactor t)) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hSlopeLower (sq_nonneg ‖x‖)
    _ = (t : ℝ)⁻¹ * ((1 - G.decayFactor t) * ‖x‖ ^ 2) := by
      ring
    _ ≤ (t : ℝ)⁻¹ *
        inner ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t x)
          x := hScaledDefect
    _ = inner ℝ
        (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
          hSymmetric t x)
        x := by
      rw [PhysicalSemigroup.vacuumOrthogonalRescaledDefect_apply,
        real_inner_smul_left]

/-- At a small positive time carrying the linear defect estimate, the rescaled
excitation defect supplies a coercive symmetric strong-limit package with the
time-independent gap `mass / 2`. -/
noncomputable def VacuumSemigroupGapSlope.vacuumOrthogonalRescaledDefectStrongLimitData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : 0 < t)
    (hLinear : (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t) :
    RealHilbertUniformCoerciveSymmetricStrongLimitData
      Unit P.VacuumOrthogonalHilbert (pure ()) :=
  { approximant := fun _ =>
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t
    limitOperator :=
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t
    gap := G.mass / 2
    gap_pos := half_pos G.mass_pos
    approximant_gap := fun _ x =>
      G.vacuumOrthogonalRescaledDefect_gap
        T hSymmetric t ht hLinear x
    strong_tendsto := fun _ => tendsto_const_nhds
    approximant_symmetric := fun _ =>
      T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect_symmetric
        hSymmetric t }

/-- For every sufficiently small positive time, the real spectrum of the
rescaled excitation defect is uniformly bounded below by `mass / 2`. -/
theorem VacuumSemigroupGapSlope.eventually_vacuumOrthogonalRescaledDefect_spectrum_subset_Ici
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t) ⊆
        Set.Ici (G.mass / 2) := by
  filter_upwards
    [G.eventually_linear_defect_lower_bound T, self_mem_nhdsWithin]
      with t hLinear ht
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_spectrum_subset_Ici
      (G.vacuumOrthogonalRescaledDefectStrongLimitData
        T hSymmetric t ht hLinear)

/-- The fixed real half-line below `mass / 2` belongs eventually to the
resolvent set of every rescaled excitation defect. -/
theorem VacuumSemigroupGapSlope.eventually_vacuumOrthogonalRescaledDefect_resolvent_halfLine
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      ∀ {lambda : ℝ}, lambda < G.mass / 2 →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t) := by
  filter_upwards
    [G.eventually_linear_defect_lower_bound T, self_mem_nhdsWithin]
      with t hLinear ht
  intro lambda hlambda
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_mem_resolventSet
      (G.vacuumOrthogonalRescaledDefectStrongLimitData
        T hSymmetric t ht hLinear)
      hlambda

/-- At each admissible positive time, the rescaled-defect resolvent has the
uniform inverse-distance estimate below `mass / 2`. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalRescaledDefect_resolvent_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : 0 < t)
    (hLinear : (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    ‖(G.vacuumOrthogonalRescaledDefectStrongLimitData
        T hSymmetric t ht hLinear).limitResolvent hlambda‖ ≤
      (G.mass / 2 - lambda)⁻¹ :=
  realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_norm_le
    (G.vacuumOrthogonalRescaledDefectStrongLimitData
      T hSymmetric t ht hLinear)
    hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- The actual finite-Wilson common-carrier route has an eventual time-uniform
`mass / 2` real spectral lower bound for the rescaled excitation defects. -/
theorem eventually_vacuumOrthogonalRescaledDefect_spectrum_subset_Ici
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t) ⊆
        Set.Ici (G.mass / 2) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.eventually_vacuumOrthogonalRescaledDefect_spectrum_subset_Ici
      T hSymmetric

/-- The actual common-carrier route also inherits the eventual fixed resolvent
half-line below `mass / 2`. -/
theorem eventually_vacuumOrthogonalRescaledDefect_resolvent_halfLine
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      ∀ {lambda : ℝ}, lambda < G.mass / 2 →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect hSymmetric t) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.eventually_vacuumOrthogonalRescaledDefect_resolvent_halfLine
      T hSymmetric

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end

end MathlibAnalytic
end MGAP4D
