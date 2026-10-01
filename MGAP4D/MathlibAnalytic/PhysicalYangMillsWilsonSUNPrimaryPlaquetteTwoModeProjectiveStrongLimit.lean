import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonEnergySUNHaarTwoMode
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNPrimaryPlaquetteProjectiveCenteredNonzeroStrongLimit
import Mathlib.Tactic

/-!
# Concrete two-mode SU(N) Wilson projective strong limit

The arbitrary-rank strong-limit theorem in #4998 still consumed an abstract
countably infinite normalized-Haar orthonormal family.  For the existence of a
single nonzero vacuum-orthogonal continuum excitation this is stronger than
needed.

For every N >= 2, #5000 theorem-generates the concrete Fin 2 orthonormal Haar
family obtained from the Wilson-energy modes 1 and E_W.  This file makes those
two modes the only Haar input.

The remaining model-facing datum contains only:

* two actual positive-time Wilson OS observables;
* their finite projective cylinder vectors;
* eventual support in the projective marginal system;
* exact finite OS/projective realization;
* exact realization of the two concrete SU(N) Wilson Haar modes.

From this finite datum we prove that at least one of the two centered actual
finite OS state sequences converges strongly to a nonzero continuum
projective-L2 vector.

No SU(2)-specific object occurs in the theorem statements.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance sunTwoModeProjectiveFiniteMarginalProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (J : Finset EuclideanFourSpace) :
    IsProbabilityMeasure (F.finiteMarginal J) :=
  F.finiteMarginalProbability J

local instance sunTwoModeProjectiveContinuumProbability
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    IsProbabilityMeasure L.continuumMeasure :=
  euclidean_yang_mills_projective_limit_probability L

/-- Model-facing realization of the two theorem-generated arbitrary-rank
Wilson Haar modes.

The normalized-Haar family itself is not a field: it is fixed by theorem to
`specialUnitaryWilsonHaarTwoMode hN2`. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N) (hN2 : 2 ≤ N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : Fin 2 → D.positiveTimeSubalgebra.toSubmodule
  cylinderIndex : Fin 2 → Finset EuclideanFourSpace
  cylinderVector : ∀ k,
    Lp ℝ 2 (F.finiteMarginal (cylinderIndex k))
  supportEventually : ∀ k,
    ∀ᶠ n in atTop, cylinderIndex k ⊆ R.marginalIndex n
  finiteImage_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)
  primaryPlaquetteWilsonTwoMode_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
        (specialUnitaryWilsonHaarTwoMode hN2 k) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Actual completed finite Wilson OS state represented by concrete mode k at
scale n. -/
noncomputable def finiteOSPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  Pn.physicalState
    (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))

/-- Named continuum projective vector represented by the source cylinder of
mode k. -/
noncomputable def continuumMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) :
    Lp ℝ 2 L.continuumMeasure :=
  L.finiteMarginalL2Pullback (C.cylinderIndex k) (C.cylinderVector k)

/-- At every containing scale, the actual finite OS state and the named
continuum vector are exactly the same projective cylinder. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) (n : ℕ)
    (hkn : C.cylinderIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n (C.finiteOSPhysicalState k n) =
      C.continuumMode k := by
  rw [R.projectiveFiniteOSEmbed_apply]
  have himage :
      R.finiteOSMarginalLinearIsometry hInvariant n
          (C.finiteOSPhysicalState k n) =
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hkn (C.cylinderVector k) := by
    simpa [finiteOSPhysicalState] using
      C.finiteImage_eq_transition k n hkn
  rw [himage]
  exact
    (L.finiteMarginalL2Pullback_compatible hkn (C.cylinderVector k)).symm

/-- The actual finite OS state sequence is eventually exactly its named
continuum mode. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) :
    (fun _ : ℕ => C.continuumMode k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n)) := by
  filter_upwards [C.supportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode
      k n hn).symm

/-- Hence each of the two actual finite OS state sequences converges strongly
in the single projective carrier. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n))
      atTop (𝓝 (C.continuumMode k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq k)

/-- Each named continuum mode has unit norm, inherited from the concrete
arbitrary-rank Wilson Haar pair. -/
@[simp] theorem continuumMode_norm
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) :
    ‖C.continuumMode k‖ = 1 := by
  obtain ⟨n, hkn⟩ := (C.supportEventually k).exists
  have hrealize := C.primaryPlaquetteWilsonTwoMode_eq_transition k n hkn
  have hhaar : ‖specialUnitaryWilsonHaarTwoMode hN2 k‖ = 1 :=
    (specialUnitaryWilsonHaarTwoMode_orthonormal hN2).norm_eq_one k
  calc
    ‖C.continuumMode k‖ = ‖C.cylinderVector k‖ := by
      exact L.finiteMarginalL2Pullback_norm
        (C.cylinderIndex k) (C.cylinderVector k)
    _ =
        ‖EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hkn (C.cylinderVector k)‖ := by
      symm
      exact LinearIsometry.norm_map _ _
    _ =
        ‖R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (specialUnitaryWilsonHaarTwoMode hN2 k)‖ := by
      rw [hrealize]
    _ = ‖specialUnitaryWilsonHaarTwoMode hN2 k‖ := by
      exact LinearIsometry.norm_map _ _
    _ = 1 := hhaar

/-- The two continuum modes remain orthogonal after projective realization. -/
theorem continuumMode_inner_eq_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    {i j : Fin 2}
    (hij : i ≠ j) :
    inner ℝ (C.continuumMode i) (C.continuumMode j) = 0 := by
  have hBoth :
      ∀ᶠ n in atTop,
        C.cylinderIndex i ⊆ R.marginalIndex n ∧
        C.cylinderIndex j ⊆ R.marginalIndex n :=
    (C.supportEventually i).and (C.supportEventually j)
  obtain ⟨n, hin, hjn⟩ := hBoth.exists
  have hi := C.primaryPlaquetteWilsonTwoMode_eq_transition i n hin
  have hj := C.primaryPlaquetteWilsonTwoMode_eq_transition j n hjn
  have hconti :=
    L.finiteMarginalL2Pullback_compatible hin (C.cylinderVector i)
  have hcontj :=
    L.finiteMarginalL2Pullback_compatible hjn (C.cylinderVector j)
  change
    inner ℝ
      (L.finiteMarginalL2Pullback (C.cylinderIndex i) (C.cylinderVector i))
      (L.finiteMarginalL2Pullback (C.cylinderIndex j) (C.cylinderVector j)) = 0
  calc
    inner ℝ
        (L.finiteMarginalL2Pullback (C.cylinderIndex i) (C.cylinderVector i))
        (L.finiteMarginalL2Pullback (C.cylinderIndex j) (C.cylinderVector j)) =
      inner ℝ
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hin (C.cylinderVector i)))
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hjn (C.cylinderVector j))) := by
      rw [hconti, hcontj]
    _ =
      inner ℝ
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hin (C.cylinderVector i))
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hjn (C.cylinderVector j)) := by
      exact L.finiteMarginalL2Pullback_inner _ _ _
    _ =
      inner ℝ
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (specialUnitaryWilsonHaarTwoMode hN2 i))
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (specialUnitaryWilsonHaarTwoMode hN2 j)) := by
      rw [hi, hj]
    _ =
      inner ℝ
        (specialUnitaryWilsonHaarTwoMode hN2 i)
        (specialUnitaryWilsonHaarTwoMode hN2 j) := by
      exact
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n).inner_map_map _ _
    _ = 0 :=
      (specialUnitaryWilsonHaarTwoMode_orthonormal hN2).inner_eq_zero hij

/-- Vacuum-centered actual finite OS state. -/
noncomputable def finiteOSCenteredPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)

/-- Vacuum-centered continuum projective mode. -/
noncomputable def centeredContinuumMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) :
    Lp ℝ 2 L.continuumMeasure :=
  finiteVacuumCentered
    (Lp.const 2 L.continuumMeasure (1 : ℝ))
    (C.continuumMode k)

/-- Every finite centered state lies in the actual finite OS
vacuum-orthogonal sector. -/
theorem finiteOSCenteredPhysicalState_mem_vacuumOrthogonal
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (k : Fin 2) (n : ℕ) :
    C.finiteOSCenteredPhysicalState k n ∈
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).vacuumOrthogonal := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  change finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n) ∈
    Pn.vacuumOrthogonal
  rw [Pn.mem_vacuumOrthogonal_iff]
  unfold finiteVacuumCentered
  have hvac : inner ℝ Pn.vacuum Pn.vacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, Pn.norm_vacuum hPn]
    norm_num
  rw [inner_sub_right, inner_smul_right, hvac]
  ring

/-- Projective embedding commutes exactly with vacuum-centering. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : Fin 2) (n : ℕ)
    (hkn : C.cylinderIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSCenteredPhysicalState k n) =
      C.centeredContinuumMode k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let vac :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let x := C.finiteOSPhysicalState k n
  have hState :
      R.projectiveFiniteOSEmbed L hInvariant n x =
        C.continuumMode k := by
    simpa [x] using
      C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumMode k n hkn
  have hVac :
      R.projectiveFiniteOSEmbed L hInvariant n vac =
        Lp.const 2 L.continuumMeasure (1 : ℝ) := by
    simpa [vac] using R.projectiveFiniteOSEmbed_vacuum_eq_one L U n
  have hInner := R.projectiveFiniteOSEmbed_inner L n vac x
  change
    R.projectiveFiniteOSEmbed L hInvariant n
      (finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)) =
      finiteVacuumCentered
        (Lp.const 2 L.continuumMeasure (1 : ℝ))
        (C.continuumMode k)
  change
    R.projectiveFiniteOSEmbed L hInvariant n
      (finiteVacuumCentered vac x) =
      finiteVacuumCentered
        (Lp.const 2 L.continuumMeasure (1 : ℝ))
        (C.continuumMode k)
  unfold finiteVacuumCentered
  rw [map_sub, map_smul, ← hInner, hState, hVac]

/-- Centered finite OS images are eventually exactly one centered continuum
mode. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : Fin 2) :
    (fun _ : ℕ => C.centeredContinuumMode k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n)) := by
  filter_upwards [C.supportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq
      U k n hn).symm

/-- The centered finite OS state sequence converges strongly to its centered
continuum mode. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : Fin 2) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n))
      atTop (𝓝 (C.centeredContinuumMode k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq U k)

/-- The projective constant-one vacuum has unit norm. -/
theorem continuumVacuum_norm
    (_C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ‖Lp.const 2 L.continuumMeasure (1 : ℝ)‖ = 1 := by
  have hv := R.projectiveFiniteOSEmbed_vacuum_eq_one L U 0
  have hnorm :=
    R.projectiveFiniteOSEmbed_norm L hInvariant 0
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant 0)
  rw [hv] at hnorm
  exact hnorm.trans
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum_norm
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant 0)

/-- At least one of the two concrete arbitrary-rank Wilson modes survives
vacuum-centering nontrivially. -/
theorem exists_centeredContinuumMode_ne_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : Fin 2, C.centeredContinuumMode k ≠ 0 := by
  have hnonzero :=
    realHilbert_exists_nonzero_finiteVacuumCentered_of_two_orthogonal_unit
      (Lp.const 2 L.continuumMeasure (1 : ℝ))
      (C.continuumMode (0 : Fin 2))
      (C.continuumMode (1 : Fin 2))
      (C.continuumVacuum_norm U)
      (C.continuumMode_norm (0 : Fin 2))
      (C.continuumMode_norm (1 : Fin 2))
      (C.continuumMode_inner_eq_zero (by decide))
  rcases hnonzero with h0 | h1
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩

/-- Concrete arbitrary-rank H1-C2 receipt: among the two theorem-generated
Wilson modes, an actual finite OS vacuum-orthogonal state sequence has a
nonzero projective strong limit. -/
theorem exists_nonzero_vacuumOrthogonal_projectiveStrongLimit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData
      S D halfExtent N hN hN2 beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : Fin 2, ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧
      Tendsto
        (fun n =>
          R.projectiveFiniteOSEmbed L hInvariant n
            (C.finiteOSCenteredPhysicalState k n))
        atTop (𝓝 y) := by
  obtain ⟨k, hy⟩ := C.exists_centeredContinuumMode_ne_zero U
  exact
    ⟨k, C.centeredContinuumMode k, hy,
      C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto U k⟩

end PhysicalYangMillsEvenPeriodicWilsonOSSUNPrimaryPlaquetteTwoModeCylinderData

end

end MathlibAnalytic
end MGAP4D
