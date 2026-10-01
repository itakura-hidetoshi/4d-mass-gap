import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonProjectiveFiniteOSScaleCoherence
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadout
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt
import Mathlib.Tactic

/-!
# Actual SU(2) primary-plaquette finite OS states have a nonzero projective strong limit

The generic projective carrier theorem of #4993 shows that coherent finite OS
states can survive as a nonzero strong limit.  This file specializes that
geometry to the already-existing SU(2) primary-plaquette Gram--Schmidt
continuum-coherent readout.

For each fixed mode `k`, the finite vector is not an abstract approximation:
it is the actual completed Wilson OS physical state represented by the
positive-time observable `C.observable k`.

The existing boundary-moment theorem identifies its selected projective
finite-marginal image with the canonical Gram--Schmidt mode.  The existing
continuum-coherence field then says that, eventually in scale, every such
finite state has exactly the same projective-limit L2 image.  Hence the
embedded finite OS states converge strongly to the named continuum cylinder
vector, whose norm is exactly one.

No independent-product coordinate is used in this argument.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance specialUnitaryTwoProjectiveStrongLimitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

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

/-- The actual completed finite Wilson OS state represented by the selected
positive-time observable at mode `k` and cutoff scale `n`. -/
noncomputable def finiteOSPhysicalState
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
  Pn.physicalState
    (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))

/-- The actual finite OS state maps to the canonical selected projective
Gram--Schmidt mode. -/
theorem finiteOSMarginalLinearIsometry_finiteOSPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    R.finiteOSMarginalLinearIsometry hInvariant n
        (C.finiteOSPhysicalState k n) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k := by
  have hBoundary :=
    C.toPointwiseCoherentReadoutData
      |>.boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2 k n
  simpa [finiteOSPhysicalState] using
    R.finiteOSMarginalLinearIsometry_physicalState_eq_primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_of_boundaryMoment
      hInvariant n k (C.observable k) hBoundary

/-- Once the source marginal of mode `k` is contained in scale `n`, the
actual finite OS state has exactly the named continuum projective-L2 image. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ)
    (hkn : R.marginalIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSPhysicalState k n) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k := by
  rw [R.projectiveFiniteOSEmbed_apply]
  rw [C.finiteOSMarginalLinearIsometry_finiteOSPhysicalState]
  exact C.primaryPlaquetteGramSchmidtMode_continuum k n hkn

/-- The named continuum Gram--Schmidt cylinder mode has unit norm. -/
@[simp] theorem primaryPlaquetteGramSchmidtContinuumL2Mode_norm
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    ‖R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k‖ = 1 := by
  unfold
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode
  rw [L.finiteMarginalL2Pullback_norm]
  exact
    (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_orthonormal k).norm_eq_one k

/-- Hence the named continuum mode is genuinely nonzero. -/
theorem primaryPlaquetteGramSchmidtContinuumL2Mode_ne_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k ≠ 0 := by
  intro hzero
  have hnorm := C.primaryPlaquetteGramSchmidtContinuumL2Mode_norm k
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- The finite projective images are eventually exactly equal to the named
continuum cylinder vector. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    (fun _ : ℕ =>
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n)) := by
  filter_upwards [C.marginalSupportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode
      k n hn).symm

/-- Therefore the actual finite Wilson OS represented states converge strongly
in the projective-limit L2 carrier to the named continuum cylinder mode. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n))
      atTop
      (𝓝
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq k)

/-- The actual finite OS representatives are eventually unit vectors as well. -/
theorem finiteOSPhysicalState_norm_eventually_eq_one
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    ∀ᶠ n in atTop, ‖C.finiteOSPhysicalState k n‖ = 1 := by
  filter_upwards [C.marginalSupportEventually k] with n hn
  have heq :=
    C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode k n hn
  calc
    ‖C.finiteOSPhysicalState k n‖ =
        ‖R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n)‖ := by
      symm
      exact
        R.projectiveFiniteOSEmbed_norm L hInvariant n
          (C.finiteOSPhysicalState k n)
    _ =
        ‖R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k‖ := by
      rw [heq]
    _ = 1 := C.primaryPlaquetteGramSchmidtContinuumL2Mode_norm k

/-- Model-facing H1-C2 receipt: for every fixed SU(2) primary-plaquette
Gram--Schmidt mode, actual completed finite Wilson OS physical states have a
nonzero projective strong limit of norm one. -/
theorem exists_nonzero_projectiveStrongLimit_of_primaryPlaquetteGramSchmidtMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧ ‖y‖ = 1 ∧
        Tendsto
          (fun n =>
            R.projectiveFiniteOSEmbed L hInvariant n
              (C.finiteOSPhysicalState k n))
          atTop (𝓝 y) := by
  refine
    ⟨R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k,
      C.primaryPlaquetteGramSchmidtContinuumL2Mode_ne_zero k,
      C.primaryPlaquetteGramSchmidtContinuumL2Mode_norm k,
      C.projectiveFiniteOSEmbed_finiteOSPhysicalState_tendsto k⟩

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
