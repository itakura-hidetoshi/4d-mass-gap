import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalProjectiveL2Carrier
import Mathlib.Tactic

/-!
# Projective finite-Wilson OS scale coherence

The independent-product carrier audit (#4988--#4992) shows that putting a
centered excitation into a fresh independent coordinate at every scale cannot
produce a nonzero strong limit.

A genuine projective-limit carrier behaves differently.  The repository
already proves exact compatibility of finite-marginal L2 pullbacks under
coordinate enlargement.  This file composes that theorem with the actual
density-corrected finite Wilson OS-to-projective-marginal isometry.

If finite Wilson OS states at successive scales agree under the canonical
projective L2 transition, their images in the continuum projective-limit L2
space are literally equal, not merely close.  Hence a coherent nonzero finite
sequence has an automatic nonzero strong limit.

The remaining model-facing task is therefore precise: construct such coherent
finite OS representatives (or an asymptotically coherent version) from the
Wilson scaling family and connect the top-orthogonal finite transfer dynamics
to them.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

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
    {L : EuclideanYangMillsProjectiveLimitMeasure F}

/-- The actual completed finite Wilson OS Hilbert space embedded directly into
one common projective-limit continuum L2 carrier.

Unlike the #4984 independent-product embedding, all scales land in the same
projective field space through finite-coordinate restriction. -/
noncomputable def projectiveFiniteOSEmbed
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.finiteMarginalL2Pullback (R.marginalIndex n)).toContinuousLinearMap.comp
    (R.finiteOSMarginalLinearIsometry hInvariant n).toContinuousLinearMap

@[simp] theorem projectiveFiniteOSEmbed_apply
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    R.projectiveFiniteOSEmbed L hInvariant n phi =
      L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.finiteOSMarginalLinearIsometry hInvariant n phi) :=
  rfl

/-- The projective-limit embedding preserves the actual finite OS norm exactly. -/
@[simp] theorem projectiveFiniteOSEmbed_norm
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n) :
    ‖R.projectiveFiniteOSEmbed L hInvariant n phi‖ = ‖phi‖ := by
  rw [R.projectiveFiniteOSEmbed_apply]
  rw [L.finiteMarginalL2Pullback_norm]
  exact R.finiteOSMarginalLinearIsometry_norm hInvariant n phi

/-- Exact projective transition compatibility of two finite OS representatives
makes their continuum projective-L2 images literally equal. -/
theorem projectiveFiniteOSEmbed_eq_of_transition
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    {n m : ℕ}
    (hnm : R.marginalIndex n ⊆ R.marginalIndex m)
    (phi :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n)
    (psi :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant m)
    (htransition :
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hnm
          (R.finiteOSMarginalLinearIsometry hInvariant n phi) =
        R.finiteOSMarginalLinearIsometry hInvariant m psi) :
    R.projectiveFiniteOSEmbed L hInvariant n phi =
      R.projectiveFiniteOSEmbed L hInvariant m psi := by
  rw [R.projectiveFiniteOSEmbed_apply, R.projectiveFiniteOSEmbed_apply]
  calc
    L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.finiteOSMarginalLinearIsometry hInvariant n phi) =
      L.finiteMarginalL2Pullback (R.marginalIndex m)
        (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) hnm
          (R.finiteOSMarginalLinearIsometry hInvariant n phi)) := by
      exact L.finiteMarginalL2Pullback_compatible hnm _
    _ =
      L.finiteMarginalL2Pullback (R.marginalIndex m)
        (R.finiteOSMarginalLinearIsometry hInvariant m psi) := by
      rw [htransition]

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- A sequence of actual completed finite Wilson OS states that is exactly
coherent under one directed family of projective finite marginals.

This is the scale-coherent analogue of the moving-coordinate sequence audited
in #4989. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
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
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) where
  state :
    (n : ℕ) →
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  marginalIndex_mono : Monotone R.marginalIndex
  transition_succ :
    ∀ n,
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) (marginalIndex_mono (Nat.le_succ n))
          (R.finiteOSMarginalLinearIsometry hInvariant n (state n)) =
        R.finiteOSMarginalLinearIsometry hInvariant (n + 1) (state (n + 1))

namespace PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence

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
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}

/-- One coherent finite state viewed in the common projective-limit continuum
L2 carrier. -/
noncomputable def continuumVector
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (n : ℕ) :
    Lp ℝ 2 L.continuumMeasure :=
  R.projectiveFiniteOSEmbed L hInvariant n (C.state n)

/-- Exact finite transition coherence makes adjacent continuum images equal. -/
theorem continuumVector_succ
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (n : ℕ) :
    C.continuumVector n = C.continuumVector (n + 1) := by
  exact
    R.projectiveFiniteOSEmbed_eq_of_transition
      L hInvariant
      (C.marginalIndex_mono (Nat.le_succ n))
      (C.state n) (C.state (n + 1))
      (C.transition_succ n)

/-- Therefore every scale has exactly the same continuum projective-L2 image
as scale zero. -/
theorem continuumVector_eq_zeroIndex
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (n : ℕ) :
    C.continuumVector n = C.continuumVector 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (C.continuumVector_succ n).symm.trans ih

/-- Exact projective coherence gives strong convergence automatically: the
continuum image sequence is constant. -/
theorem continuumVector_tendsto
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L) :
    Tendsto C.continuumVector atTop (𝓝 (C.continuumVector 0)) := by
  have hfun :
      C.continuumVector = fun _ : ℕ => C.continuumVector 0 := by
    funext n
    exact C.continuumVector_eq_zeroIndex n
  rw [hfun]
  exact tendsto_const_nhds

/-- The continuum image has the same norm as the actual finite OS state at
every scale. -/
@[simp] theorem continuumVector_norm
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (n : ℕ) :
    ‖C.continuumVector n‖ = ‖C.state n‖ := by
  exact R.projectiveFiniteOSEmbed_norm L hInvariant n (C.state n)

/-- A nonzero initial finite OS state therefore gives a genuinely nonzero
continuum strong limit. -/
theorem continuumVector_zero_ne_zero
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (h0 : C.state 0 ≠ 0) :
    C.continuumVector 0 ≠ 0 := by
  intro hzero
  have hnorm := C.continuumVector_norm 0
  rw [hzero, norm_zero] at hnorm
  exact h0 (norm_eq_zero.mp hnorm.symm)

/-- Audit-visible contrast with #4989: exact projective coherence supports a
nonzero strong limit whenever the initial finite OS state is nonzero. -/
theorem exists_nonzero_projective_strongLimit
    (C : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence
      R L)
    (h0 : C.state 0 ≠ 0) :
    ∃ y : Lp ℝ 2 L.continuumMeasure,
      y ≠ 0 ∧ Tendsto C.continuumVector atTop (𝓝 y) :=
  ⟨C.continuumVector 0, C.continuumVector_zero_ne_zero h0,
    C.continuumVector_tendsto⟩

end PhysicalYangMillsEvenPeriodicWilsonOSProjectiveCoherentFiniteSequence

end

end MathlibAnalytic
end MGAP4D
