import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

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

/-- A continuum vacuum-sector semigroup gap in the infinitesimal slope form.

The scalar `decayFactor t` is the transfer contraction visible at Euclidean time
`t`.  The condition

`((t : ℝ)⁻¹ * (1 - decayFactor t)) → mass`

as positive time tends to zero is the form stable under a scale-dependent
renormalized transfer trajectory.  It is deliberately more general than fixing
`decayFactor t = exp (-mass * t)` in advance. -/
structure VacuumSemigroupGapSlope
    (T : P.StronglyContinuousPhysicalSemigroup) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : NNReal → ℝ
  slope_tendsto :
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  decay : ∀ (t : NNReal) (psi : P.PhysicalHilbert),
    inner ℝ psi P.vacuum = 0 →
      ‖T.toPhysicalSemigroup.operator t psi‖ ≤
        decayFactor t * ‖psi‖

/-- Finite-volume transfer operators with one uniform vacuum-sector gap slope,
together with norm convergence of states and evolved states to the completed OS
Hilbert space.

This is the exact transport boundary needed between a finite-volume transfer
operator estimate and the continuum semigroup.  The finite spaces may vary with
volume; only scalar norms are compared across scales. -/
structure FiniteVolumeVacuumGapTransfer
    (T : P.StronglyContinuousPhysicalSemigroup) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : NNReal → ℝ
  slope_tendsto :
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  FiniteState : ℕ → Type
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteState n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteState n)]
  finiteVacuum : (n : ℕ) → FiniteState n
  finiteOperator :
    (n : ℕ) → NNReal → FiniteState n →L[ℝ] FiniteState n
  approximate :
    (n : ℕ) → P.PhysicalHilbert →L[ℝ] FiniteState n
  approximate_orthogonal :
    ∀ (n : ℕ) (psi : P.PhysicalHilbert),
      inner ℝ psi P.vacuum = 0 →
        inner ℝ (approximate n psi) (finiteVacuum n) = 0
  approximate_norm_tendsto :
    ∀ psi : P.PhysicalHilbert,
      Tendsto (fun n : ℕ => ‖approximate n psi‖)
        atTop (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.PhysicalHilbert),
      Tendsto
        (fun n : ℕ => ‖finiteOperator n t (approximate n psi)‖)
        atTop
        (nhds ‖T.toPhysicalSemigroup.operator t psi‖)
  finite_decay :
    ∀ (n : ℕ) (t : NNReal) (phi : FiniteState n),
      inner ℝ phi (finiteVacuum n) = 0 →
        ‖finiteOperator n t phi‖ ≤ decayFactor t * ‖phi‖

attribute [instance]
  FiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  FiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace FiniteVolumeVacuumGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- A uniform finite-volume transfer gap passes to the continuum completed OS
semigroup by scalar norm convergence. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.FiniteVolumeVacuumGapTransfer) :
    T.VacuumSemigroupGapSlope where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  decay := by
    intro t psi hpsi
    apply le_of_tendsto_of_tendsto
      (G.evolved_norm_tendsto t psi)
      (tendsto_const_nhds.mul (G.approximate_norm_tendsto psi))
    exact Filter.Eventually.of_forall fun n =>
      G.finite_decay n t (G.approximate n psi)
        (G.approximate_orthogonal n psi hpsi)

end FiniteVolumeVacuumGapTransfer

/-- The canonical right OS Hamiltonian has Rayleigh quotient at least `mass` on
the orthogonal complement of the vacuum whenever the continuum semigroup has a
vacuum-sector gap slope.

The proof is the infinitesimal transfer-operator argument.  Cauchy--Schwarz and
the semigroup decay estimate bound the Hamiltonian difference quotient from
below by

`((t : ℝ)⁻¹ * (1 - decayFactor t)) * ‖psi‖²`.

Both sides then converge as positive time tends to zero. -/
theorem VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  have hHamiltonian :
      Tendsto
        (fun t : NNReal =>
          T.rightHamiltonianDifferenceQuotient
            (psi : P.PhysicalHilbert) t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (T.rightHamiltonian psi)) := by
    have hGenerator := T.rightGenerator_hasRightGeneratorValue psi
    unfold HasRightGeneratorValue at hGenerator
    simpa only [T.rightHamiltonianDifferenceQuotient_eq_neg,
      T.rightHamiltonian_apply] using hGenerator.neg
  have hSlope :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ * (1 - G.decayFactor t)) *
            ‖(psi : P.PhysicalHilbert)‖ ^ 2)
        (nhdsWithin 0 (Ioi 0))
        (nhds (G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2)) :=
    G.slope_tendsto.mul tendsto_const_nhds
  have hInner :
      Tendsto
        (fun t : NNReal =>
          inner ℝ
            (T.rightHamiltonianDifferenceQuotient
              (psi : P.PhysicalHilbert) t)
            (psi : P.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (inner ℝ (T.rightHamiltonian psi)
            (psi : P.PhysicalHilbert))) :=
    hHamiltonian.inner tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hSlope hInner
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htReal.le
  have hdecay := G.decay t (psi : P.PhysicalHilbert) hpsi
  have hinnerBound :
      inner ℝ
          (T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert))
          (psi : P.PhysicalHilbert) ≤
        G.decayFactor t * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    calc
      inner ℝ
          (T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert))
          (psi : P.PhysicalHilbert) ≤
          ‖T.toPhysicalSemigroup.operator t
              (psi : P.PhysicalHilbert)‖ *
            ‖(psi : P.PhysicalHilbert)‖ :=
        real_inner_le_norm _ _
      _ ≤
          (G.decayFactor t * ‖(psi : P.PhysicalHilbert)‖) *
            ‖(psi : P.PhysicalHilbert)‖ :=
        mul_le_mul_of_nonneg_right hdecay (norm_nonneg _)
      _ = G.decayFactor t * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
        ring
  have hsub :
      (1 - G.decayFactor t) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 -
          inner ℝ
            (T.toPhysicalSemigroup.operator t
              (psi : P.PhysicalHilbert))
            (psi : P.PhysicalHilbert) := by
    calc
      (1 - G.decayFactor t) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 =
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 -
            G.decayFactor t * ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
        ring
      _ ≤
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 -
            inner ℝ
              (T.toPhysicalSemigroup.operator t
                (psi : P.PhysicalHilbert))
              (psi : P.PhysicalHilbert) :=
        sub_le_sub_left hinnerBound _
  calc
    ((t : ℝ)⁻¹ * (1 - G.decayFactor t)) *
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 =
        (t : ℝ)⁻¹ *
          ((1 - G.decayFactor t) *
            ‖(psi : P.PhysicalHilbert)‖ ^ 2) := by
      ring
    _ ≤
        (t : ℝ)⁻¹ *
          (‖(psi : P.PhysicalHilbert)‖ ^ 2 -
            inner ℝ
              (T.toPhysicalSemigroup.operator t
                (psi : P.PhysicalHilbert))
              (psi : P.PhysicalHilbert)) :=
      mul_le_mul_of_nonneg_left hsub hinv
    _ =
        inner ℝ
          (T.rightHamiltonianDifferenceQuotient
            (psi : P.PhysicalHilbert) t)
          (psi : P.PhysicalHilbert) := by
      simp only [rightHamiltonianDifferenceQuotient,
        real_inner_smul_left, inner_sub_left,
        real_inner_self_eq_norm_sq]
      ring

/-- The finite-volume transfer package therefore yields the canonical continuum
Hamiltonian mass-gap inequality on the vacuum-orthogonal generator domain. -/
theorem FiniteVolumeVacuumGapTransfer.rightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope psi hpsi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
