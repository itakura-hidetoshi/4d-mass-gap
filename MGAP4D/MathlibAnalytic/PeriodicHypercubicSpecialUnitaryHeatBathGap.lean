import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathPoincareL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Connect the native compact-Haar heat-bath Hamiltonian and Poincaré theory to the
actual finite periodic `SU(N)` Wilson systems.

Unlike the earlier concrete `Z₂` exact-gap instantiation, every configuration
and Gibbs measure in this file is built from
`Matrix.specialUnitaryGroup (Fin N) ℂ` and normalized Haar integration.
-/

/-- The native compact-group heat-bath Poincaré inequality specialized to the
canonical finite periodic `SU(N)` Wilson system. -/
def periodicHypercubicSpecialUnitaryHeatBathPoincareL2
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (gap : ℝ) : Prop :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg).HeatBathPoincareL2 gap

/-- The finite periodic `SU(N)` heat-bath Hamiltonian is symmetric in the real
Gibbs `L²` pairing. -/
theorem periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_inner_symm
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (f g : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure) :
    inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).heatBathHamiltonianL2 f) g =
      inner ℝ f
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).heatBathHamiltonianL2 g) :=
  continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg) f g

/-- The finite periodic `SU(N)` heat-bath Hamiltonian has nonnegative quadratic
form. -/
theorem periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_nonneg
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure) :
    0 ≤ inner ℝ
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).heatBathHamiltonianL2 f) f :=
  continuous_compact_oriented_heatBathHamiltonianL2_nonneg
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg) f

/-- The normalized Haar--Gibbs vacuum of the finite periodic `SU(N)` system has
unit norm. -/
theorem periodicHypercubicSpecialUnitary_gibbsVacuumL2_norm
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ‖(periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).gibbsVacuumL2‖ = 1 :=
  continuous_compact_oriented_gibbsVacuumL2_norm
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg)

/-- The native finite periodic `SU(N)` heat-bath Hamiltonian annihilates the
normalized Haar--Gibbs vacuum. -/
theorem periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_vacuum
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).heatBathHamiltonianL2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).gibbsVacuumL2 = 0 :=
  continuous_compact_oriented_heatBathHamiltonianL2_vacuum
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg)

/-- A periodic `SU(N)` heat-bath Poincaré inequality gives the exact coercive
Hamiltonian lower bound on every vector orthogonal to the Haar--Gibbs vacuum. -/
theorem periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (gap : ℝ)
    (hPoincare : periodicHypercubicSpecialUnitaryHeatBathPoincareL2
      n N hN beta beta_nonneg gap)
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure)
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsVacuumL2 f = 0) :
    gap * ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).heatBathHamiltonianL2 f) f := by
  exact
    continuous_compact_oriented_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      gap hPoincare f hf

/-- With a strictly positive periodic `SU(N)` Poincaré constant, the
vacuum-orthogonal kernel of the native heat-bath Hamiltonian is trivial. -/
theorem periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hPoincare : periodicHypercubicSpecialUnitaryHeatBathPoincareL2
      n N hN beta beta_nonneg gap)
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure)
    (hfOrth : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsVacuumL2 f = 0)
    (hfZero :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).heatBathHamiltonianL2 f = 0) :
    f = 0 := by
  exact
    continuous_compact_oriented_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      gap hgap hPoincare f hfOrth hfZero

/-- One scale-independent Poincaré constant for the full periodic `SU(N)`
Wilson approximation family.  This is the precise non-Abelian finite-side datum
needed before passing the compact Haar heat-bath gap into an OS continuum
construction. -/
structure PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n) where
  gap : ℝ
  gap_pos : 0 < gap
  poincare :
    ∀ (n : ℕ) [NeZero n],
      periodicHypercubicSpecialUnitaryHeatBathPoincareL2
        n N hN (beta n) (beta_nonneg n) gap

namespace PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData

/-- Uniform non-Abelian Poincaré data produce the same coercive lower bound at
every positive periodic lattice size. -/
theorem coercive
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsMeasure)
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsVacuumL2 f = 0) :
    D.gap * ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN (beta n) (beta_nonneg n)).heatBathHamiltonianL2 f) f :=
  periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    n N hN (beta n) (beta_nonneg n) D.gap (D.poincare n) f hf

/-- Uniform positive `SU(N)` heat-bath gap data exclude nonzero zero-energy
vectors orthogonal to the Haar--Gibbs vacuum at every finite scale. -/
theorem kernel_eq_vacuum_on_orthogonal
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsMeasure)
    (hfOrth : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsVacuumL2 f = 0)
    (hfZero :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).heatBathHamiltonianL2 f = 0) :
    f = 0 :=
  periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
    n N hN (beta n) (beta_nonneg n) D.gap D.gap_pos
    (D.poincare n) f hfOrth hfZero

end PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData

end

end MathlibAnalytic
end MGAP4D
