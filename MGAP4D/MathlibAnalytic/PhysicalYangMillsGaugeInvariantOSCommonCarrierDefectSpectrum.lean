import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSemigroupDefectSpectrum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

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

/-- The actual Wilson common-carrier transfer package supplies the continuum
vacuum-sector semigroup gap slope used by the bounded excitation-defect
spectral API. -/
noncomputable def toContinuumVacuumSemigroupGapSlope
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G) :
    T.VacuumSemigroupGapSlope :=
  A.toEmbeddedFiniteVolumeVacuumGapTransfer.toVacuumSemigroupGapSlope

/-- At every positive-time scale with strict transferred contraction, the
actual Wilson common-carrier construction bounds the real spectrum of the
vacuum-orthogonal defect `I - T(t)` below by `1 - decayFactor(t)`. -/
theorem vacuumOrthogonalDefect_spectrum_subset_Ici
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1) :
    spectrum ℝ
        (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
      Set.Ici (1 - G.decayFactor t) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.vacuumOrthogonalDefect_spectrum_subset_Ici T hSymmetric t ht

/-- Every real parameter below the transferred positive-time contraction
deficit belongs to the excitation-defect resolvent set. -/
theorem vacuumOrthogonalDefect_mem_resolventSet
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1)
    {lambda : ℝ}
    (hlambda : lambda < 1 - G.decayFactor t) :
    lambda ∈ resolventSet ℝ
      (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.vacuumOrthogonalDefect_mem_resolventSet
      T hSymmetric t ht hlambda

/-- The Wilson common-carrier excitation-defect resolvent obeys the sharp
inverse-distance norm estimate inherited from the transferred contraction
deficit. -/
theorem vacuumOrthogonalDefect_resolvent_norm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1)
    {lambda : ℝ}
    (hlambda : lambda < 1 - G.decayFactor t) :
    ‖(A.toContinuumVacuumSemigroupGapSlope
        |>.vacuumOrthogonalDefectStrongLimitData T hSymmetric t ht).limitResolvent
        hlambda‖ ≤
      (1 - G.decayFactor t - lambda)⁻¹ :=
  A.toContinuumVacuumSemigroupGapSlope
    |>.vacuumOrthogonalDefect_resolvent_norm_le
      T hSymmetric t ht hlambda

/-- Bundled bounded-spectrum conclusion for the actual finite-Wilson to
continuum common-carrier route. -/
theorem vacuumOrthogonalDefect_spectral_package
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal)
    (ht : G.decayFactor t < 1) :
    spectrum ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) ⊆
        Set.Ici (1 - G.decayFactor t) ∧
      ∀ {lambda : ℝ}, lambda < 1 - G.decayFactor t →
        lambda ∈ resolventSet ℝ
          (T.toPhysicalSemigroup.vacuumOrthogonalDefect hSymmetric t) := by
  constructor
  · exact A.vacuumOrthogonalDefect_spectrum_subset_Ici
      hSymmetric t ht
  · intro lambda hlambda
    exact A.vacuumOrthogonalDefect_mem_resolventSet
      hSymmetric t ht hlambda

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end

end MathlibAnalytic
end MGAP4D
