import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveDefectTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A positive infinitesimal vacuum-sector mass gives an eventually linear
lower bound for the positive-time contraction deficit. -/
theorem VacuumSemigroupGapSlope.eventually_linear_defect_lower_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      (G.mass / 2) * (t : ℝ) ≤ 1 - G.decayFactor t := by
  have hEventuallySlope :
      ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
        G.mass / 2 < (t : ℝ)⁻¹ * (1 - G.decayFactor t) :=
    (tendsto_order.1 G.slope_tendsto).1
      (G.mass / 2) (by linarith [G.mass_pos])
  filter_upwards [hEventuallySlope, self_mem_nhdsWithin] with t htSlope htPos
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast htPos
  have htSlopeDiv :
      G.mass / 2 < (1 - G.decayFactor t) / (t : ℝ) := by
    simpa [inv_mul_eq_div] using htSlope
  exact ((lt_div_iff₀ htReal).mp htSlopeDiv).le

/-- For every sufficiently small positive Euclidean time, the excitation-sector
semigroup defect has a real spectral gap at least `(mass / 2) * t`. -/
theorem VacuumSemigroupGapSlope.eventually_vacuumOrthogonalDefect_spectrum_subset_Ici_linear
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
        Set.Ici ((G.mass / 2) * (t : ℝ)) := by
  filter_upwards
    [G.eventually_linear_defect_lower_bound T, self_mem_nhdsWithin]
      with t hLinear htPos
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast htPos
  have hLinearPos : 0 < (G.mass / 2) * (t : ℝ) :=
    mul_pos (half_pos G.mass_pos) htReal
  have hDeficitPos : 0 < 1 - G.decayFactor t :=
    hLinearPos.trans_le hLinear
  have htDecay : G.decayFactor t < 1 := sub_pos.mp hDeficitPos
  intro lambda hlambdaSpectrum
  have hDeficitLeLambda :
      1 - G.decayFactor t ≤ lambda :=
    (G.vacuumOrthogonalDefect_spectrum_subset_Ici
      T hSymmetric t htDecay) hlambdaSpectrum
  exact hLinear.trans hDeficitLeLambda

/-- The corresponding small-time linear half-line lies in the real resolvent
set of the excitation defect. -/
theorem VacuumSemigroupGapSlope.eventually_vacuumOrthogonalDefect_linear_resolvent_halfLine
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      ∀ {lambda : ℝ}, lambda < (G.mass / 2) * (t : ℝ) →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) := by
  filter_upwards
    [G.eventually_linear_defect_lower_bound T, self_mem_nhdsWithin]
      with t hLinear htPos
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast htPos
  have hLinearPos : 0 < (G.mass / 2) * (t : ℝ) :=
    mul_pos (half_pos G.mass_pos) htReal
  have hDeficitPos : 0 < 1 - G.decayFactor t :=
    hLinearPos.trans_le hLinear
  have htDecay : G.decayFactor t < 1 := sub_pos.mp hDeficitPos
  intro lambda hlambda
  exact G.vacuumOrthogonalDefect_mem_resolventSet
    T hSymmetric t htDecay (hlambda.trans_le hLinear)

/-- The small-time spectral and resolvent conclusions may be consumed together
without reopening the slope-limit argument. -/
theorem VacuumSemigroupGapSlope.eventually_vacuumOrthogonalDefect_linear_spectral_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      spectrum ℝ
            (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
          Set.Ici ((G.mass / 2) * (t : ℝ)) ∧
        ∀ {lambda : ℝ}, lambda < (G.mass / 2) * (t : ℝ) →
          lambda ∈ resolventSet ℝ
            (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) :=
  (G.eventually_vacuumOrthogonalDefect_spectrum_subset_Ici_linear
      T hSymmetric).and
    (G.eventually_vacuumOrthogonalDefect_linear_resolvent_halfLine
      T hSymmetric)

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

/-- The actual finite-Wilson common-carrier route inherits the eventual linear
small-time defect-spectrum gap from its positive transferred mass slope. -/
theorem eventually_vacuumOrthogonalDefect_spectrum_subset_Ici_linear
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
        Set.Ici ((G.mass / 2) * (t : ℝ)) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.eventually_vacuumOrthogonalDefect_spectrum_subset_Ici_linear
      T hSymmetric

/-- The actual common-carrier route also inherits the eventual linear resolvent
half-line below `(mass / 2) * t`. -/
theorem eventually_vacuumOrthogonalDefect_linear_resolvent_halfLine
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
      ∀ {lambda : ℝ}, lambda < (G.mass / 2) * (t : ℝ) →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.eventually_vacuumOrthogonalDefect_linear_resolvent_halfLine
      T hSymmetric

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end

end MathlibAnalytic
end MGAP4D
