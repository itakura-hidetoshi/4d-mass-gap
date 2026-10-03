import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredCommonImageVacuumReduction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPositiveHalfCanonicalSign
import Mathlib.Tactic

/-!
# Canonical-sign OS vacuum pair has the constant-one projective image

After #5071, strong convergence of the projected physical non-top excitation
was reduced to two moving common-carrier sequences:

1. the canonical-sign finite OS vacuum-pair image;
2. the physical pair-top image.

The first sequence is not merely convergent. It is exactly the same
constant-one continuum vector at every finite scale.

The projective boundary readout structure depends on the positive-half bridge
Q only as a phantom parameter: its actual fields are the selected marginal,
the boundary readout, measurability, and the interacting boundary marginal law.
Therefore the same readout can be retyped canonically from Q to
Q.vacuumNormalized.

For that canonical-sign readout, the existing
projectiveFiniteOSEmbed_vacuum_eq_one theorem applies. The pair-coordinate
vacuum is exactly the boundary vacuum transported through the
boundary-Haar/pair-Haar linear isometry, whose inverse recovers the original
boundary vector. Hence the pair-Haar common-carrier embedding is literally the
finite-OS projective vacuum embedding and equals constant one.

Consequently the only remaining strong-convergence sequence from #5071 is the
physical pair-top common image.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Retype a projective boundary readout along canonical sign normalization.

The readout fields themselves are unchanged because the interacting boundary
marginal depends only on the finite Wilson parameters, not on the sign choice
of the positive-half square root. -/
noncomputable def vacuumNormalized
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q.vacuumNormalized F where
  marginalIndex := R.marginalIndex
  boundaryReadout := R.boundaryReadout
  boundaryReadout_measurable := R.boundaryReadout_measurable
  map_finiteMarginal_eq_boundaryMarginal :=
    R.map_finiteMarginal_eq_boundaryMarginal

@[simp] theorem vacuumNormalized_marginalIndex
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    R.vacuumNormalized.marginalIndex n = R.marginalIndex n :=
  rfl

@[simp] theorem vacuumNormalized_boundaryReadout
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    R.vacuumNormalized.boundaryReadout n = R.boundaryReadout n :=
  rfl

/-- Density-corrected boundary-Haar projective embedding is unchanged by
canonical sign normalization. -/
theorem vacuumNormalized_boundaryHaarProjectiveL2Isometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    R.vacuumNormalized.boundaryHaarProjectiveL2Isometry n =
      R.boundaryHaarProjectiveL2Isometry n :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

local instance vacuumPairProjectiveOneTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumPairProjectiveOneCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumPairProjectiveOneSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumPairProjectiveOneMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumPairProjectiveOneBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumPairProjectiveOneSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance vacuumPairProjectiveOneSpatialHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section VacuumPairProjectiveOne

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- At every scale, the canonical-sign finite OS vacuum pair has exactly the
constant-one image in the common projective continuum L2 carrier. -/
theorem
    physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_eq_one
    (n : ℕ) :
    physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
        Q hInvariant R L n =
      Lp.const 2 L.continuumMeasure (1 : ℝ) := by
  let Rv := R.vacuumNormalized
  let vac :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant n
  let J :=
    Q.vacuumNormalized.physicalHilbertBoundaryMomentLinearIsometry
      hInvariant n
  let E :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
      (halfExtent n) N
  have hPair :
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent n) N
          (E (J vac)) =
        J vac := by
    simpa [E] using
      periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse
        (halfExtent n) N (J vac)
  have hFactor :
      Rv.finiteOSMarginalLinearIsometry hInvariant n vac =
        Rv.boundaryHaarProjectiveL2Isometry n (J vac) := by
    simpa [J, vac] using
      (Rv.finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry_sun
        hInvariant n vac)
  have hVacuum :
      Rv.projectiveFiniteOSEmbed L hInvariant n vac =
        Lp.const 2 L.continuumMeasure (1 : ℝ) := by
    simpa [vac] using
      (Rv.projectiveFiniteOSEmbed_vacuum_eq_one
        L (Q.vacuumNormalizedUnitCompatibility hInvariant) n)
  change
    L.finiteMarginalL2Pullback (R.marginalIndex n)
      (R.boundaryHaarProjectiveL2Isometry n
        (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
          (halfExtent n) N (E (J vac)))) =
      Lp.const 2 L.continuumMeasure (1 : ℝ)
  rw [hPair]
  change
    L.finiteMarginalL2Pullback (Rv.marginalIndex n)
      (Rv.boundaryHaarProjectiveL2Isometry n (J vac)) =
      Lp.const 2 L.continuumMeasure (1 : ℝ)
  rw [← hFactor]
  simpa [Rv, PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout.projectiveFiniteOSEmbed_apply]
    using hVacuum

/-- Hence the OS-vacuum pair common image is strongly constant along every
scale map, without any cofinality assumption. -/
theorem
    physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_tendsto_one
    (scale : ℕ → ℕ) :
    Tendsto
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
          Q hInvariant R L (scale j))
      atTop
      (𝓝 (Lp.const 2 L.continuumMeasure (1 : ℝ))) := by
  have hEq :
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage
          Q hInvariant R L (scale j)) =
        fun _ : ℕ => Lp.const 2 L.continuumMeasure (1 : ℝ) := by
    funext j
    exact
      physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_eq_one
        Q hInvariant R L (scale j)
  rw [hEq]
  exact tendsto_const_nhds

/-- Post-#5071 reduction with the vacuum sequence discharged: along any cofinal
scale map, convergence of the physical pair-top common image alone implies
strong convergence of the canonical projected physical non-top excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_of_top_tendsto
    {hN2 : 2 ≤ N}
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModePointwiseCoherentReadoutData
        S D halfExtent N hN hN2 beta hbeta Q F R hInvariant)
    (k : Fin 2)
    (scale : ℕ → ℕ)
    (hScale : Tendsto scale atTop atTop)
    (topLimit : Lp ℝ 2 L.continuumMeasure)
    (hTop :
      Tendsto
        (fun j =>
          physicalYangMillsSUNPhysicalPairTopContinuumImage
            (Q := Q) R L (scale j))
        atTop
        (𝓝 topLimit)) :
    Tendsto
      (fun j =>
        physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage
          (hN2 := hN2) Q hInvariant R L k (scale j))
      atTop
      (𝓝
        (let centeredLimit :=
          finiteVacuumCentered
            (Lp.const 2 L.continuumMeasure (1 : ℝ))
            ((C.toTwoModeCylinderData L).continuumMode k)
        centeredLimit - inner ℝ topLimit centeredLimit • topLimit)) := by
  exact
    physicalYangMillsVacuumNormalizedSUNTwoModeProjectedNonTopContinuumImage_tendsto_of_vacuumPair_top_tendsto
      (hN2 := hN2) Q hInvariant R L C k scale hScale
      (Lp.const 2 L.continuumMeasure (1 : ℝ)) topLimit
      (physicalYangMillsVacuumNormalizedSUNOSVacuumPairContinuumImage_tendsto_one
        Q hInvariant R L scale)
      hTop

end VacuumPairProjectiveOne

end

end MathlibAnalytic
end MGAP4D
