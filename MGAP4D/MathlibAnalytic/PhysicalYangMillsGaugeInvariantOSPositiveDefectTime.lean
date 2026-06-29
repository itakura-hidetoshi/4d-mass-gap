import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierDefectSpectrum

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

/-- A positive vacuum-sector infinitesimal gap slope forces a strict contraction
at some positive Euclidean time. -/
theorem VacuumSemigroupGapSlope.exists_pos_decayFactor_lt_one
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope) :
    ∃ t : NNReal, 0 < t ∧ G.decayFactor t < 1 := by
  have hHalfPos : 0 < G.mass / 2 := half_pos G.mass_pos
  have hEventuallySlope :
      ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
        G.mass / 2 < (t : ℝ)⁻¹ * (1 - G.decayFactor t) :=
    (tendsto_order.1 G.slope_tendsto).1
      (G.mass / 2) (by linarith)
  have hEventuallyBoth :
      ∀ᶠ t : NNReal in nhdsWithin 0 (Ioi 0),
        G.mass / 2 < (t : ℝ)⁻¹ * (1 - G.decayFactor t) ∧
          t ∈ Ioi (0 : NNReal) :=
    hEventuallySlope.and self_mem_nhdsWithin
  obtain ⟨t, htSlope, htPos⟩ := hEventuallyBoth.exists
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast htPos
  have hSlopePos :
      0 < (t : ℝ)⁻¹ * (1 - G.decayFactor t) :=
    hHalfPos.trans htSlope
  have hDeficitPos : 0 < 1 - G.decayFactor t := by
    by_contra hNotPos
    have hDeficitNonpos : 1 - G.decayFactor t ≤ 0 :=
      le_of_not_gt hNotPos
    have hProductNonpos :
        (t : ℝ)⁻¹ * (1 - G.decayFactor t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.mpr htReal.le) hDeficitNonpos
    linarith
  exact ⟨t, htPos, sub_pos.mp hDeficitPos⟩

/-- Consequently, a positive mass slope supplies at least one bounded
vacuum-orthogonal semigroup defect with a genuine positive lower real spectrum
bound. -/
theorem VacuumSemigroupGapSlope.exists_vacuumOrthogonalDefect_spectrum_gap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∃ t : NNReal,
      0 < t ∧
      G.decayFactor t < 1 ∧
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
        Set.Ici (1 - G.decayFactor t) := by
  obtain ⟨t, htPos, htDecay⟩ := G.exists_pos_decayFactor_lt_one T
  exact
    ⟨t, htPos, htDecay,
      G.vacuumOrthogonalDefect_spectrum_subset_Ici
        T hSymmetric t htDecay⟩

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

/-- The actual finite-Wilson common-carrier construction automatically supplies
a positive Euclidean time at which the continuum excitation defect has a
strict positive real spectral lower bound. -/
theorem exists_vacuumOrthogonalDefect_spectrum_gap
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∃ t : NNReal,
      0 < t ∧
      G.decayFactor t < 1 ∧
      spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
        Set.Ici (1 - G.decayFactor t) := by
  exact
    A.toContinuumVacuumSemigroupGapSlope
      |>.exists_vacuumOrthogonalDefect_spectrum_gap T hSymmetric

/-- At the automatically selected strict-contraction time, every real parameter
below the defect gap lies in the resolvent set. -/
theorem exists_vacuumOrthogonalDefect_resolvent_halfLine
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    ∃ t : NNReal,
      0 < t ∧
      G.decayFactor t < 1 ∧
      ∀ {lambda : ℝ}, lambda < 1 - G.decayFactor t →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) := by
  obtain ⟨t, htPos, htDecay⟩ :=
    A.toContinuumVacuumSemigroupGapSlope
      |>.exists_pos_decayFactor_lt_one T
  refine ⟨t, htPos, htDecay, ?_⟩
  intro lambda hlambda
  exact A.vacuumOrthogonalDefect_mem_resolventSet
    hSymmetric t htDecay hlambda

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end

end MathlibAnalytic
end MGAP4D
