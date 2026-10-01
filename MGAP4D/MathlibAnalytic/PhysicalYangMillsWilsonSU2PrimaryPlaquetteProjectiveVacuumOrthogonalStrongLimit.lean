import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteProjectiveStrongLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import MGAP4D.MathlibAnalytic.RealL2MeasurePreservingConstant
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap
import Mathlib.Tactic

/-!
# Projective vacuum coherence and centered SU(2) primary-plaquette strong limits

PR #4994 constructs nonzero projective strong limits of actual completed finite
Wilson OS states. This file adds the vacuum geometry needed to turn that
scale-coherent ambient statement into an excitation-sector statement.

Projective pullback, unlike fresh independent-coordinate embedding, preserves
the canonical constant-one vector. Combined with the existing positive-half
vacuum-unit compatibility, every finite OS vacuum is therefore sent to one and
the same constant-one vector in the projective-limit continuum L2 carrier.

Consequently finite vacuum-centering commutes with the projective embedding.
For every fixed SU(2) primary-plaquette Gram--Schmidt mode, the centered finite
OS representatives are eventually exactly equal to one named centered
continuum vector, hence converge strongly to it.

No spectral-gap or continuum-time decay estimate is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance projectiveVacuumOrthogonalStrongLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance projectiveVacuumOrthogonalStrongLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance projectiveVacuumOrthogonalStrongLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance projectiveVacuumOrthogonalStrongLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance projectiveVacuumOrthogonalStrongLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance projectiveVacuumOrthogonalStrongLimitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace EuclideanYangMillsProjectiveLimitMeasure

variable {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Canonical projective finite-marginal pullback fixes the constant-one L2
vector. Thus all finite vacuum representatives normalized to one share one
continuum vacuum candidate. -/
theorem finiteMarginalL2Pullback_const_one
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (J : Finset EuclideanFourSpace) :
    L.finiteMarginalL2Pullback J
        (Lp.const 2 (F.finiteMarginal J) (1 : ℝ)) =
      Lp.const 2 L.continuumMeasure (1 : ℝ) := by
  letI : IsProbabilityMeasure (F.finiteMarginal J) :=
    F.finiteMarginalProbability J
  letI : IsProbabilityMeasure L.continuumMeasure :=
    euclidean_yang_mills_projective_limit_probability L
  change
    Lp.compMeasurePreservingₗᵢ ℝ J.restrict
        (projectiveLimitRestrictionMeasurePreserving
          L.continuumMeasure F.finiteMarginal L.projectiveLimit J)
        (Lp.const 2 (F.finiteMarginal J) (1 : ℝ)) =
      Lp.const 2 L.continuumMeasure (1 : ℝ)
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
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Pullback from the actual interacting boundary marginal to the chosen finite
projective marginal fixes the constant-one vector. -/
theorem boundaryMarginalL2Pullback_const_one
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (n : ℕ) :
    R.boundaryMarginalL2Pullback n
        (Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            (halfExtent n) N hN (beta n) (hbeta n))
          (1 : ℝ)) =
      Lp.const 2
        (F.finiteMarginal (R.marginalIndex n))
        (1 : ℝ) := by
  letI : IsProbabilityMeasure
      (F.finiteMarginal (R.marginalIndex n)) :=
    F.finiteMarginalProbability (R.marginalIndex n)
  change
    Lp.compMeasurePreservingₗᵢ ℝ
        (R.boundaryReadout n)
        (R.boundaryReadoutMeasurePreserving n)
        (Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            (halfExtent n) N hN (beta n) (hbeta n))
          (1 : ℝ)) =
      Lp.const 2
        (F.finiteMarginal (R.marginalIndex n))
        (1 : ℝ)
  exact
    realL2_compMeasurePreserving_const_one
      (R.boundaryReadout n)
      (R.boundaryReadoutMeasurePreserving n)

/-- The direct projective finite-OS embedding preserves inner products exactly. -/
theorem projectiveFiniteOSEmbed_inner
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi psi :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    inner ℝ
      (R.projectiveFiniteOSEmbed L hInvariant n phi)
      (R.projectiveFiniteOSEmbed L hInvariant n psi) =
        inner ℝ phi psi := by
  rw [R.projectiveFiniteOSEmbed_apply, R.projectiveFiniteOSEmbed_apply]
  rw [L.finiteMarginalL2Pullback_inner]
  exact
    (R.finiteOSMarginalLinearIsometry hInvariant n).inner_map_map phi psi

/-- Under finite vacuum-unit normalization, every finite OS vacuum has the same
projective-limit continuum image: constant one. -/
theorem projectiveFiniteOSEmbed_vacuum
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) =
      Lp.const 2 L.continuumMeasure (1 : ℝ) := by
  rw [R.projectiveFiniteOSEmbed_apply]
  change
    L.finiteMarginalL2Pullback (R.marginalIndex n)
      (R.boundaryMarginalL2Pullback n
        (Q.physicalHilbertBoundaryMarginalLinearIsometry hInvariant n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n))) =
      Lp.const 2 L.continuumMeasure (1 : ℝ)
  rw [U.toBoundaryMarginalVacuumCompatibility.finite_vacuum_eq_one n]
  rw [R.boundaryMarginalL2Pullback_const_one n]
  exact L.finiteMarginalL2Pullback_const_one (R.marginalIndex n)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Canonical vacuum vector in the projective-limit continuum L2 carrier. -/
noncomputable def physicalYangMillsProjectiveContinuumVacuum
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    Lp ℝ 2 L.continuumMeasure :=
  Lp.const 2 L.continuumMeasure (1 : ℝ)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- Vacuum-centered continuum representative of the k-th SU(2)
primary-plaquette Gram--Schmidt cylinder mode. -/
noncomputable def primaryPlaquetteGramSchmidtContinuumCenteredL2Mode
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (k : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  finiteVacuumCentered
    (physicalYangMillsProjectiveContinuumVacuum L)
    (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k)

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

/-- Vacuum-centered actual finite OS representative of the selected
primary-plaquette mode. -/
noncomputable def finiteOSVacuumCenteredPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)

/-- Every finite centered representative lies in the actual finite OS
vacuum-orthogonal sector. -/
theorem finiteOSVacuumCenteredPhysicalState_mem_vacuumOrthogonal
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    C.finiteOSVacuumCenteredPhysicalState k n ∈
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
  change finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n) ∈
    Pn.vacuumOrthogonal
  rw [Pn.mem_vacuumOrthogonal_iff]
  unfold finiteVacuumCentered
  have hvac : inner ℝ Pn.vacuum Pn.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, Pn.norm_vacuum hPn]
    norm_num
  simp [inner_sub_right, real_inner_smul_right, hvac]

/-- Under finite vacuum-unit normalization, projective embedding commutes
exactly with vacuum-centering once scale n contains the source marginal of
mode k. -/
theorem projectiveFiniteOSEmbed_finiteOSVacuumCenteredPhysicalState_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k n : ℕ)
    (hkn : R.marginalIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSVacuumCenteredPhysicalState k n) =
      R.primaryPlaquetteGramSchmidtContinuumCenteredL2Mode L k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let vac :=
    physicalYangMillsProjectiveContinuumVacuum L
  let mode :=
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k
  have hstate :
      R.projectiveFiniteOSEmbed L hInvariant n (C.finiteOSPhysicalState k n) =
        mode := by
    simpa [mode] using
      C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode k n hkn
  have hvac :
      R.projectiveFiniteOSEmbed L hInvariant n Pn.vacuum = vac := by
    simpa [Pn, vac, physicalYangMillsProjectiveContinuumVacuum] using
      R.projectiveFiniteOSEmbed_vacuum L hInvariant U n
  have hinner :
      inner ℝ Pn.vacuum (C.finiteOSPhysicalState k n) =
        inner ℝ vac mode := by
    calc
      inner ℝ Pn.vacuum (C.finiteOSPhysicalState k n) =
          inner ℝ
            (R.projectiveFiniteOSEmbed L hInvariant n Pn.vacuum)
            (R.projectiveFiniteOSEmbed L hInvariant n
              (C.finiteOSPhysicalState k n)) := by
        symm
        exact
          R.projectiveFiniteOSEmbed_inner L hInvariant n
            Pn.vacuum (C.finiteOSPhysicalState k n)
      _ = inner ℝ vac mode := by rw [hvac, hstate]
  change
    R.projectiveFiniteOSEmbed L hInvariant n
        (finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)) =
      finiteVacuumCentered vac mode
  unfold finiteVacuumCentered
  rw [map_sub, map_smul, hstate, hvac, hinner]

/-- Centered finite OS states are eventually exactly one centered continuum
projective vector. -/
theorem projectiveFiniteOSEmbed_finiteOSVacuumCenteredPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    (fun _ : ℕ =>
      R.primaryPlaquetteGramSchmidtContinuumCenteredL2Mode L k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSVacuumCenteredPhysicalState k n)) := by
  filter_upwards [C.marginalSupportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSVacuumCenteredPhysicalState_eq
      U k n hn).symm

/-- Actual finite vacuum-orthogonal representatives have a strong limit in the
scale-coherent projective carrier. -/
theorem projectiveFiniteOSEmbed_finiteOSVacuumCenteredPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSVacuumCenteredPhysicalState k n))
      atTop
      (𝓝 (R.primaryPlaquetteGramSchmidtContinuumCenteredL2Mode L k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSVacuumCenteredPhysicalState_eventually_eq
      U k)

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
