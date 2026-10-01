import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteProjectiveStrongLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalProbabilityMeasure
import MGAP4D.MathlibAnalytic.RealL2MeasurePreservingConstant
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredQuadraticExcitation
import Mathlib.Tactic

/-!
# Vacuum-centered SU(2) primary-plaquette projective strong limits

PR #4994 constructed nonzero projective strong limits for the actual completed
finite Wilson OS states represented by the continuum-coherent SU(2)
primary-plaquette Gram--Schmidt observables.

This file adds the vacuum sector needed before any finite transfer-gap estimate
can be transported through that carrier.

Under the already-isolated positive-half vacuum-unit compatibility, the actual
finite OS vacuum maps first to constant one in the interacting boundary
marginal, then to constant one in the selected projective finite marginal, and
finally to constant one in the projective-limit continuum L2 space.

Consequently finite vacuum-centering commutes exactly with the projective
embedding.  For every fixed primary-plaquette mode the vacuum-centered finite
OS states are eventually represented by one fixed vacuum-centered continuum
vector, hence converge strongly to it.  The finite centered states lie in the
actual finite OS vacuum-orthogonal sector.

No one-slab top-sector identification and no quantitative gap estimate is used
here.  Those remain the next H1-D/H1-C3 bridge.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance projectiveCenteredStrongLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance projectiveCenteredStrongLimitSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance projectiveCenteredStrongLimitFiniteMarginalProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure (F.finiteMarginal J) :=
  F.finiteMarginalProbability J

local instance projectiveCenteredStrongLimitContinuumProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

namespace EuclideanYangMillsProjectiveLimitMeasure

variable {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Projective-limit finite-coordinate pullback preserves the canonical
constant-one real L2 vector exactly. -/
@[simp] theorem finiteMarginalL2Pullback_const_one
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J : Finset EuclideanFourSpace) :
    L.finiteMarginalL2Pullback J
        (Lp.const 2 (F.finiteMarginal J) (1 : ℝ)) =
      Lp.const 2 L.continuumMeasure (1 : ℝ) := by
  unfold EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Pullback
  exact
    realL2_compMeasurePreserving_const_one
      J.restrict
      (projectiveLimitRestrictionMeasurePreserving
        L.continuumMeasure F.finiteMarginal L.projectiveLimit J)

end EuclideanYangMillsProjectiveLimitMeasure

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Once the finite Wilson OS vacuum is normalized to constant one in the
interacting boundary marginal, its selected projective finite-marginal image
is also exactly constant one. -/
@[simp] theorem finiteOSMarginalLinearIsometry_vacuum_eq_one
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    R.finiteOSMarginalLinearIsometry hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      Lp.const 2 (F.finiteMarginal (R.marginalIndex n)) (1 : ℝ) := by
  change
    R.boundaryMarginalL2Pullback n
        (Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)) =
      Lp.const 2 (F.finiteMarginal (R.marginalIndex n)) (1 : ℝ)
  rw [U.toBoundaryMarginalVacuumCompatibility.finite_vacuum_eq_one n]
  unfold boundaryMarginalL2Pullback
  exact
    realL2_compMeasurePreserving_const_one
      (R.boundaryReadout n)
      (R.boundaryReadoutMeasurePreserving n)

/-- The common projective-limit embedding therefore sends every finite Wilson
OS vacuum to one and the same continuum constant-one vector. -/
@[simp] theorem projectiveFiniteOSEmbed_vacuum_eq_one
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      Lp.const 2 L.continuumMeasure (1 : ℝ) := by
  rw [R.projectiveFiniteOSEmbed_apply]
  rw [R.finiteOSMarginalLinearIsometry_vacuum_eq_one U n]
  exact L.finiteMarginalL2Pullback_const_one (R.marginalIndex n)

/-- The projective finite-OS embedding preserves real inner products exactly,
not only norms. -/
@[simp] theorem projectiveFiniteOSEmbed_inner
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (n : ℕ)
    (phi psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    inner ℝ
        (R.projectiveFiniteOSEmbed L hInvariant n phi)
        (R.projectiveFiniteOSEmbed L hInvariant n psi) =
      inner ℝ phi psi :=
  ContinuousLinearMap.inner_map_map_of_norm_map
    (R.projectiveFiniteOSEmbed L hInvariant n)
    (R.projectiveFiniteOSEmbed_norm L hInvariant n)
    phi psi

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Vacuum-center the actual completed finite Wilson OS primary-plaquette state
at cutoff scale n. -/
noncomputable def finiteOSCenteredPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n :=
  finiteVacuumCentered
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n)
    (C.finiteOSPhysicalState k n)

/-- The continuum vector obtained by centering the named projective
primary-plaquette cylinder mode against continuum constant one. -/
noncomputable def primaryPlaquetteGramSchmidtCenteredContinuumL2Mode
    (_C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  finiteVacuumCentered
    (Lp.const 2 L.continuumMeasure (1 : ℝ))
    (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k)

/-- Every finite centered state lies in the actual completed finite Wilson OS
vacuum-orthogonal sector. -/
theorem finiteOSCenteredPhysicalState_mem_vacuumOrthogonal
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    C.finiteOSCenteredPhysicalState k n ∈
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n).vacuumOrthogonal := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  rw [Pn.mem_vacuumOrthogonal_iff]
  change
    inner ℝ Pn.vacuum
      (finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)) = 0
  unfold finiteVacuumCentered
  have hvac : inner ℝ Pn.vacuum Pn.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, Pn.norm_vacuum hPn]
    norm_num
  rw [inner_sub_right, inner_smul_right, hvac]
  ring

/-- Under finite vacuum normalization, projective embedding commutes exactly
with vacuum-centering of the actual primary-plaquette finite OS state. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq_centeredContinuumMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k n : ℕ)
    (hkn : R.marginalIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSCenteredPhysicalState k n) =
      C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode k := by
  let vac :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let x := C.finiteOSPhysicalState k n
  have hState :
      R.projectiveFiniteOSEmbed L hInvariant n x =
        R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k := by
    simpa [x] using
      C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode k n hkn
  have hVac :
      R.projectiveFiniteOSEmbed L hInvariant n vac =
        Lp.const 2 L.continuumMeasure (1 : ℝ) := by
    simpa [vac] using R.projectiveFiniteOSEmbed_vacuum_eq_one L U n
  have hInner :=
    R.projectiveFiniteOSEmbed_inner L n vac x
  unfold finiteOSCenteredPhysicalState
  unfold primaryPlaquetteGramSchmidtCenteredContinuumL2Mode
  unfold finiteVacuumCentered
  change
    R.projectiveFiniteOSEmbed L hInvariant n
        (x - inner ℝ vac x • vac) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k -
        inner ℝ (Lp.const 2 L.continuumMeasure (1 : ℝ))
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k) •
        Lp.const 2 L.continuumMeasure (1 : ℝ)
  rw [map_sub, map_smul]
  rw [← hInner]
  rw [hState, hVac]

/-- The projective images of the finite centered states are eventually exactly
equal to one fixed centered continuum cylinder vector. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    (fun _ : ℕ => C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n)) := by
  filter_upwards [C.marginalSupportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq_centeredContinuumMode
      U k n hn).symm

/-- Hence the actual finite Wilson OS vacuum-centered representatives converge
strongly in the scale-coherent projective-limit L2 carrier. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n))
      atTop
      (𝓝 (C.primaryPlaquetteGramSchmidtCenteredContinuumL2Mode k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq U k)

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
