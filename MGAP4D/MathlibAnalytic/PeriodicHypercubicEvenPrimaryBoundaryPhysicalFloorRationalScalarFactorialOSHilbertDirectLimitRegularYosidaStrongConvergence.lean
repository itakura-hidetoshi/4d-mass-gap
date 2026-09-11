import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaDomainConvergence
import Mathlib.Tactic

/-!
# Strong Yosida convergence on the full same-root regular OS Hilbert sector

The preceding layer proves strong convergence of the dyadic normalized Yosida resolvents

`J_{2^n} = 2^n (2^n I + H̄)⁻¹`

on the dense closed-Hamiltonian domain.  Since every `J_λ` is a contraction, the standard
three-term density estimate extends this convergence to every vector of the complete regular
Hilbert sector.

On `dom(H̄)` the bounded Yosida Hamiltonians satisfy

`H_λ x = J_λ (H̄ x)`.

Applying full-space strong convergence to `H̄ x` therefore yields

`H_{2^n} x → H̄ x`.

No new analytic hypothesis, spectral functional calculus, or exponential-semigroup identity is
introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Dyadic Yosida resolvents converge strongly to the identity on the whole regular Hilbert sector. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y)
      atTop (nhds y) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hepsilon3 : 0 < epsilon / 3 := by positivity
  obtain ⟨z, hz, hyz⟩ :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_dense_domain.exists_dist_lt
      y hepsilon3
  let x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain := ⟨z, hz⟩
  have hcore :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto_on_closedDomain x
  rw [Metric.tendsto_nhds] at hcore
  have hcoreEventually := hcore (epsilon / 3) hepsilon3
  filter_upwards [hcoreEventually] with n hn
  have hleft :
      dist (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y)
          (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n z) ≤
        dist y z := by
    change
      dist
          (P.fixedSlotHilbertDirectLimitRegularYosidaResolvent
            (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
            (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) y)
          (P.fixedSlotHilbertDirectLimitRegularYosidaResolvent
            (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
            (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) z) ≤
        dist y z
    simpa only [dist_eq_norm, map_sub] using
      P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_bound
        (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
        (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) (y - z)
  have hmiddle :
      dist (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n z) z <
        epsilon / 3 := by
    simpa [x] using hn
  have hright : dist z y < epsilon / 3 := by
    simpa [dist_comm] using hyz
  calc
    dist (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y) y ≤
        dist (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y)
            (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n z) +
          dist (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n z) z +
          dist z y := dist_triangle4 _ _ _ _
    _ < epsilon := by linarith

/-- Equivalent full-space defect formulation: `y - J_{2^n} y → 0`. -/
theorem fixedSlotHilbertDirectLimitRegular_sub_dyadicYosidaResolvent_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ => y - P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y)
      atTop (nhds 0) := by
  have hconst : Tendsto (fun _ : ℕ => y) atTop (nhds y) := tendsto_const_nhds
  have hJ := P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto y
  simpa using hconst.sub hJ

/-- Dyadic bounded Yosida Hamiltonian `H_{2^n}`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian
    (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
    (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n)

/-- On the closed Hamiltonian domain, bounded dyadic Yosida Hamiltonians converge strongly to `H̄`. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_closedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)) := by
  have hJ := P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)
  have hfun :
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)) := by
    funext n
    change
      P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n)
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) =
        P.fixedSlotHilbertDirectLimitRegularYosidaResolvent
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
          (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n)
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)
    exact P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) x
  rw [hfun]
  exact hJ

/-- Full-space/dense-domain Yosida strong-convergence package. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaStrongConvergence_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (∀ y : P.fixedSlotHilbertDirectLimitRegularSubspace,
      Tendsto
        (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n y)
        atTop (nhds y)) ∧
    (∀ x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain,
      Tendsto
        (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
        atTop
        (nhds (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x))) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto,
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_closedDomain⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
