import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPrimaryPlaquetteHaarModeProjectiveCylinder
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteProjectiveCenteredStrongLimit
import Mathlib.Tactic

/-!
# Generic SU(N) projective vacuum-orthogonal strong limits

The SU(2) primary-plaquette lane established the geometry of a nonzero centered
projective strong limit.  This file removes the rank-two specialization.

The input is the repository's existing
`PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData`,
which is already formulated for arbitrary `SU(N)`.  It contains actual
positive-time Wilson OS observables, one normalized-Haar orthonormal holonomy
mode family, exact primary-plaquette realization, and projective finite-marginal
coherence.

From these data we prove:

* each finite Wilson OS represented state has an eventual exact continuum
  projective image;
* distinct continuum Haar modes remain orthogonal and every mode has norm one;
* finite vacuum-centering commutes with projective embedding under the existing
  positive-half vacuum-unit compatibility;
* the centered finite states lie in the actual finite OS vacuum-orthogonal
  sector;
* at least one of the first two centered continuum modes is nonzero;
* hence there exists an actual nonzero strong limit of finite
  vacuum-orthogonal Wilson OS states.

No `N = 2` assumption occurs in the theorem statements.  The next model-facing
step is to construct the primary-plaquette Haar-mode cylinder datum uniformly
for every rank `N >= 2` from explicit `SU(N)` Wilson class functions.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

/-- Two orthogonal unit vectors cannot both lie on one unit vacuum line.
Equivalently, at least one has a nonzero vacuum-centered component. -/
theorem realHilbert_exists_nonzero_finiteVacuumCentered_of_two_orthogonal_unit
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (vac e0 e1 : E)
    (hvac : ‖vac‖ = 1)
    (he0norm : ‖e0‖ = 1)
    (he1norm : ‖e1‖ = 1)
    (he01 : inner ℝ e0 e1 = 0) :
    finiteVacuumCentered vac e0 ≠ 0 ∨
      finiteVacuumCentered vac e1 ≠ 0 := by
  by_contra h
  push_neg at h
  rcases h with ⟨h0zero, h1zero⟩
  let a0 : ℝ := inner ℝ vac e0
  let a1 : ℝ := inner ℝ vac e1
  have he0 : e0 = a0 • vac := by
    unfold finiteVacuumCentered at h0zero
    simpa [a0] using (sub_eq_zero.mp h0zero)
  have he1 : e1 = a1 • vac := by
    unfold finiteVacuumCentered at h1zero
    simpa [a1] using (sub_eq_zero.mp h1zero)
  have ha0 : a0 ≠ 0 := by
    intro ha0
    have he0zero : e0 = 0 := by simpa [ha0] using he0
    rw [he0zero, norm_zero] at he0norm
    norm_num at he0norm
  have ha1 : a1 ≠ 0 := by
    intro ha1
    have he1zero : e1 = 0 := by simpa [ha1] using he1
    rw [he1zero, norm_zero] at he1norm
    norm_num at he1norm
  have hvacinner : inner ℝ vac vac = 1 := by
    rw [real_inner_self_eq_norm_sq, hvac]
    norm_num
  have hmul : a0 * a1 = 0 := by
    have horth := he01
    rw [he0, he1, real_inner_smul_left, real_inner_smul_right, hvacinner] at horth
    simpa [mul_assoc] using horth
  exact (mul_ne_zero ha0 ha1) hmul

namespace PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData

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
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Actual completed finite Wilson OS state represented by mode `k` at scale
`n`. -/
noncomputable def finiteOSPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  Pn.physicalState
    (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))

/-- Canonical continuum projective vector represented by the source finite
marginal of mode `k`. -/
noncomputable def continuumHaarMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  L.finiteMarginalL2Pullback (C.cylinderIndex k) (C.cylinderVector k)

/-- Once scale `n` contains the source cylinder support, the actual finite OS
state has exactly the named continuum projective image. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumHaarMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k n : ℕ)
    (hkn : C.cylinderIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSPhysicalState k n) =
      C.continuumHaarMode k := by
  rw [R.projectiveFiniteOSEmbed_apply]
  rw [C.finiteImage_eq_transition k n hkn]
  exact
    (L.finiteMarginalL2Pullback_compatible hkn (C.cylinderVector k)).symm

/-- The actual finite OS images are eventually exactly equal to their named
continuum projective mode. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    (fun _ : ℕ => C.continuumHaarMode k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n)) := by
  filter_upwards [C.supportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumHaarMode
      k n hn).symm

/-- Therefore every actual finite Wilson OS Haar-mode sequence converges
strongly to its named projective continuum mode. -/
theorem projectiveFiniteOSEmbed_finiteOSPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSPhysicalState k n))
      atTop (𝓝 (C.continuumHaarMode k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eventually_eq k)

/-- Every continuum Haar mode has unit norm. -/
@[simp] theorem continuumHaarMode_norm
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    ‖C.continuumHaarMode k‖ = 1 := by
  obtain ⟨n, hkn⟩ := (C.supportEventually k).exists
  have hrealize := C.primaryPlaquetteHaarMode_eq_transition k n hkn
  have hhaar : ‖C.haarMode k‖ = 1 :=
    C.haarMode_orthonormal.norm_eq_one k
  calc
    ‖C.continuumHaarMode k‖ = ‖C.cylinderVector k‖ := by
      exact L.finiteMarginalL2Pullback_norm
        (C.cylinderIndex k) (C.cylinderVector k)
    _ =
        ‖EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hkn (C.cylinderVector k)‖ := by
      symm
      exact LinearIsometry.norm_map _ _
    _ =
        ‖R.primarySpatialPlaquetteHaarProjectiveL2Isometry n
          (C.haarMode k)‖ := by
      rw [hrealize]
    _ = ‖C.haarMode k‖ := by
      exact LinearIsometry.norm_map _ _
    _ = 1 := hhaar

/-- Distinct continuum Haar modes remain orthogonal in the single projective
limit carrier. -/
theorem continuumHaarMode_inner_eq_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    {i j : ℕ}
    (hij : i ≠ j) :
    inner ℝ (C.continuumHaarMode i) (C.continuumHaarMode j) = 0 := by
  have hBoth :
      ∀ᶠ n in atTop,
        C.cylinderIndex i ⊆ R.marginalIndex n ∧
        C.cylinderIndex j ⊆ R.marginalIndex n :=
    (C.supportEventually i).and (C.supportEventually j)
  obtain ⟨n, hin, hjn⟩ := hBoth.exists
  have hi := C.primaryPlaquetteHaarMode_eq_transition i n hin
  have hj := C.primaryPlaquetteHaarMode_eq_transition j n hjn
  have hconti :=
    L.finiteMarginalL2Pullback_compatible hin (C.cylinderVector i)
  have hcontj :=
    L.finiteMarginalL2Pullback_compatible hjn (C.cylinderVector j)
  calc
    inner ℝ (C.continuumHaarMode i) (C.continuumHaarMode j) =
      inner ℝ
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hin (C.cylinderVector i)))
        (L.finiteMarginalL2Pullback (R.marginalIndex n)
          (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
            (F := F) hjn (C.cylinderVector j))) := by
      rw [← hconti, ← hcontj]
    _ =
      inner ℝ
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hin (C.cylinderVector i))
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hjn (C.cylinderVector j)) := by
      exact L.finiteMarginalL2Pullback_inner _ _ _
    _ =
      inner ℝ
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n (C.haarMode i))
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n (C.haarMode j)) := by
      rw [hi, hj]
    _ = inner ℝ (C.haarMode i) (C.haarMode j) := by
      exact
        (R.primarySpatialPlaquetteHaarProjectiveL2Isometry n).inner_map_map
          (C.haarMode i) (C.haarMode j)
    _ = 0 := C.haarMode_orthonormal.inner_eq_zero hij

/-- Vacuum-centered actual finite OS state for mode `k`. -/
noncomputable def finiteOSCenteredPhysicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n :=
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)

/-- Vacuum-centered continuum Haar mode. -/
noncomputable def centeredContinuumHaarMode
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  finiteVacuumCentered
    (Lp.const 2 L.continuumMeasure (1 : ℝ))
    (C.continuumHaarMode k)

/-- Every finite centered state lies in the actual finite Wilson OS
vacuum-orthogonal sector. -/
theorem finiteOSCenteredPhysicalState_mem_vacuumOrthogonal
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
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

/-- Under the existing finite vacuum-unit normalization, projective embedding
commutes exactly with vacuum-centering. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k n : ℕ)
    (hkn : C.cylinderIndex k ⊆ R.marginalIndex n) :
    R.projectiveFiniteOSEmbed L hInvariant n
        (C.finiteOSCenteredPhysicalState k n) =
      C.centeredContinuumHaarMode k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let vac :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let x := C.finiteOSPhysicalState k n
  have hState :
      R.projectiveFiniteOSEmbed L hInvariant n x =
        C.continuumHaarMode k := by
    simpa [x] using
      C.projectiveFiniteOSEmbed_finiteOSPhysicalState_eq_continuumHaarMode
        k n hkn
  have hVac :
      R.projectiveFiniteOSEmbed L hInvariant n vac =
        Lp.const 2 L.continuumMeasure (1 : ℝ) := by
    simpa [vac] using R.projectiveFiniteOSEmbed_vacuum_eq_one L U n
  have hInner :=
    R.projectiveFiniteOSEmbed_inner L n vac x
  change
    R.projectiveFiniteOSEmbed L hInvariant n
      (finiteVacuumCentered Pn.vacuum (C.finiteOSPhysicalState k n)) =
      finiteVacuumCentered
        (Lp.const 2 L.continuumMeasure (1 : ℝ))
        (C.continuumHaarMode k)
  change
    R.projectiveFiniteOSEmbed L hInvariant n
      (finiteVacuumCentered vac x) =
      finiteVacuumCentered
        (Lp.const 2 L.continuumMeasure (1 : ℝ))
        (C.continuumHaarMode k)
  unfold finiteVacuumCentered
  rw [map_sub, map_smul]
  rw [← hInner]
  rw [hState, hVac]

/-- Centered finite OS images are eventually exactly one centered continuum
mode. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    (fun _ : ℕ => C.centeredContinuumHaarMode k) =ᶠ[atTop]
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n)) := by
  filter_upwards [C.supportEventually k] with n hn
  exact
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eq
      U k n hn).symm

/-- Actual finite vacuum-orthogonal Wilson OS states therefore converge
strongly to the centered continuum Haar mode. -/
theorem projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (k : ℕ) :
    Tendsto
      (fun n =>
        R.projectiveFiniteOSEmbed L hInvariant n
          (C.finiteOSCenteredPhysicalState k n))
      atTop (𝓝 (C.centeredContinuumHaarMode k)) := by
  exact tendsto_const_nhds.congr'
    (C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_eventually_eq U k)

/-- The continuum constant-one vacuum has unit norm. -/
theorem projectiveContinuumVacuum_norm
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
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

/-- At least one of the first two continuum Haar modes has a nonzero centered
component.  This is rank-independent. -/
theorem exists_centeredContinuumHaarMode_ne_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : ℕ, (k = 0 ∨ k = 1) ∧ C.centeredContinuumHaarMode k ≠ 0 := by
  have hnonzero :=
    realHilbert_exists_nonzero_finiteVacuumCentered_of_two_orthogonal_unit
      (Lp.const 2 L.continuumMeasure (1 : ℝ))
      (C.continuumHaarMode 0)
      (C.continuumHaarMode 1)
      (C.projectiveContinuumVacuum_norm U)
      (C.continuumHaarMode_norm 0)
      (C.continuumHaarMode_norm 1)
      (C.continuumHaarMode_inner_eq_zero (by norm_num))
  rcases hnonzero with h0 | h1
  · exact ⟨0, ⟨Or.inl rfl, h0⟩⟩
  · exact ⟨1, ⟨Or.inr rfl, h1⟩⟩

/-- Generic SU(N) H1-C2 receipt: actual finite Wilson OS vacuum-orthogonal
states admit a nonzero projective strong limit. -/
theorem exists_nonzero_vacuumOrthogonal_projectiveStrongLimit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData
      S D halfExtent N hN beta hbeta Q F R L hInvariant)
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant) :
    ∃ k : ℕ, ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧
      Tendsto
        (fun n =>
          R.projectiveFiniteOSEmbed L hInvariant n
            (C.finiteOSCenteredPhysicalState k n))
        atTop (𝓝 y) := by
  obtain ⟨k, _hk, hy⟩ := C.exists_centeredContinuumHaarMode_ne_zero U
  exact
    ⟨k, C.centeredContinuumHaarMode k, hy,
      C.projectiveFiniteOSEmbed_finiteOSCenteredPhysicalState_tendsto U k⟩

end PhysicalYangMillsEvenPeriodicWilsonOSPrimaryPlaquetteHaarModeCylinderData

end

end MathlibAnalytic
end MGAP4D
