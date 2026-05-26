import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessInput

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The completed graph-energy prefix deficit is eventually small.

This is the Mathlib-clean tail-control step extracted from prefix convergence:
finite prefixes converge to the completed `tsum`, and the prefix-order theorem
says each finite prefix is below the completed energy.  Therefore the absolute
error in the prefix convergence is exactly the nonnegative deficit
`completed - prefix`, so it is eventually below every positive `ε`.
-/
theorem concrete_l2_completed_graph_energy_prefix_deficit_eventually_small
    (p : ConcreteL2GraphPairSpace) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop,
      concreteL2CompletedGraphEnergy p -
        Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) < ε := by
  have hclose := concrete_l2_completed_graph_energy_prefix_eventually_close p ε hε
  filter_upwards [hclose] with N hN
  have hle :
      Finset.sum (Finset.range N)
        (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
        concreteL2CompletedGraphEnergy p := by
    exact concrete_l2_graph_energy_range_prefix_le_completed p N
  have habs :
      |Finset.sum (Finset.range N)
          (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) -
        concreteL2CompletedGraphEnergy p| =
        concreteL2CompletedGraphEnergy p -
          Finset.sum (Finset.range N)
            (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  simpa [habs] using hN

/--
Specialization of prefix-deficit smallness to the diagonal target graph of a
diagonal-domain point.
-/
theorem concrete_l2_diagonal_target_graph_prefix_deficit_eventually_small
    (x : ConcreteL2DiagonalDomainCarrier) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop,
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) -
        Finset.sum (Finset.range N)
          (fun n : ℕ =>
            concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) < ε := by
  exact concrete_l2_completed_graph_energy_prefix_deficit_eventually_small
    (x.1, concreteL2DiagonalActionL2 x) ε hε

/--
Square-ε specialization for the diagonal target graph.  This is the exact
numerical scale needed by the energy-ε route to graph-norm density.
-/
theorem concrete_l2_diagonal_target_graph_prefix_deficit_eventually_lt_eps_sq
    (x : ConcreteL2DiagonalDomainCarrier) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop,
      concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) -
        Finset.sum (Finset.range N)
          (fun n : ℕ =>
            concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) < ε ^ 2 := by
  exact concrete_l2_diagonal_target_graph_prefix_deficit_eventually_small
    x (ε ^ 2) (pow_pos hε 2)

/--
The prefix-deficit smallness package needed before turning truncation-error
energy into an actual tail estimate.
-/
def concreteL2MathlibSpectralAuditR2PrefixDeficitSmallPackage : Prop :=
  (∀ p : ConcreteL2GraphPairSpace,
    ∀ ε : ℝ,
      0 < ε →
        ∀ᶠ N in Filter.atTop,
          concreteL2CompletedGraphEnergy p -
            Finset.sum (Finset.range N)
              (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) < ε) ∧
  (∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ ε : ℝ,
      0 < ε →
        ∀ᶠ N in Filter.atTop,
          concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) -
            Finset.sum (Finset.range N)
              (fun n : ℕ =>
                concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) < ε ^ 2)

/-- The prefix-deficit smallness package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_prefix_deficit_small_package_ready :
    concreteL2MathlibSpectralAuditR2PrefixDeficitSmallPackage := by
  exact ⟨
    concrete_l2_completed_graph_energy_prefix_deficit_eventually_small,
    concrete_l2_diagonal_target_graph_prefix_deficit_eventually_lt_eps_sq⟩

/--
Boundary retained after prefix-deficit smallness.

This proves the convergent-prefix deficit estimate, but still does not identify
the completed truncation-error energy with that deficit.  That exact
identification is the next theorem needed to close the tail-smallness target.
-/
def concreteL2MathlibSpectralAuditR2PrefixDeficitSmallBoundaryHeld : Prop :=
  True

/-- Surface for prefix-deficit smallness. -/
structure ConcreteL2MathlibSpectralAuditR2PrefixDeficitSmallSurface where
  tailSmallnessInputReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessInputSurfaceReady
  prefixDeficitSmallPackage :
    concreteL2MathlibSpectralAuditR2PrefixDeficitSmallPackage
  boundaryHeld : concreteL2MathlibSpectralAuditR2PrefixDeficitSmallBoundaryHeld
  boundaryNotTruncationErrorEqualsTailDeficit : Prop
  boundaryNotTailSmallnessTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotExactAtomDerivation : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete prefix-deficit smallness surface. -/
def concreteL2MathlibSpectralAuditR2PrefixDeficitSmallSurface :
    ConcreteL2MathlibSpectralAuditR2PrefixDeficitSmallSurface :=
  { tailSmallnessInputReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_input_surface_ready
    prefixDeficitSmallPackage :=
      concrete_l2_mathlib_spectral_audit_r2_prefix_deficit_small_package_ready
    boundaryHeld := True.intro
    boundaryNotTruncationErrorEqualsTailDeficit := True
    boundaryNotTailSmallnessTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotExactAtomDerivation := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the prefix-deficit smallness surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2PrefixDeficitSmallSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2TailSmallnessInputSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2PrefixDeficitSmallPackage ∧
  concreteL2MathlibSpectralAuditR2PrefixDeficitSmallBoundaryHeld

/-- Readiness theorem for the prefix-deficit smallness surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_prefix_deficit_small_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2PrefixDeficitSmallSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_tail_smallness_input_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_prefix_deficit_small_package_ready,
    True.intro⟩

end

end MathlibAnalytic
end MGAP4D
