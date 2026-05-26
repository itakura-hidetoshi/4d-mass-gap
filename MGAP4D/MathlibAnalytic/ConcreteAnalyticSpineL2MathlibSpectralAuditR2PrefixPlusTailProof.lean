import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2PrefixPlusTailReduction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Prefix plus outside-cutoff tail equals the completed target energy. -/
theorem concrete_l2_prefix_plus_tail_eq_completed_target
    (x : ConcreteL2DiagonalDomainCarrier) (N : Nat) :
    Finset.sum (Finset.range N)
        (fun n : Nat =>
          concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n) +
      tsum (fun n : Nat => concreteL2TargetGraphEnergyTailIte x N n) =
        concreteL2CompletedGraphEnergy (x.1, concreteL2DiagonalActionL2 x) := by
  let f : Nat -> Real :=
    fun n : Nat => concreteL2GraphPairEnergyTerm (x.1, concreteL2DiagonalActionL2 x) n
  let s : Set Nat := (Finset.range N : Set Nat)
  have hsFinite : s.Finite := by
    simp [s]
  have hs : Summable (f ∘ (Subtype.val : s -> Nat)) := by
    exact hsFinite.summable f
  have hsc : Summable (f ∘ (Subtype.val : {n : Nat // n ∈ sᶜ} -> Nat)) := by
    rw [summable_subtype_iff_indicator]
    simpa [s, f, concreteL2TargetGraphEnergyTailIte, Set.indicator]
      using concrete_l2_target_graph_energy_tail_ite_summable x N
  have hsplit := Summable.tsum_add_tsum_compl (s := s) hs hsc
  have hprefix :
      (tsum fun n : s => f n.1) =
        Finset.sum (Finset.range N) (fun n : Nat => f n) := by
    simpa [s] using Finset.tsum_subtype (Finset.range N) f
  have htail :
      (tsum fun n : {n : Nat // n ∈ sᶜ} => f n.1) =
        tsum (fun n : Nat => concreteL2TargetGraphEnergyTailIte x N n) := by
    rw [tsum_subtype]
    apply tsum_congr
    intro n
    by_cases hn : n < N
    · simp [s, f, concreteL2TargetGraphEnergyTailIte, Set.indicator, hn]
    · simp [s, f, concreteL2TargetGraphEnergyTailIte, Set.indicator, hn]
  simpa [concreteL2CompletedGraphEnergy, f, hprefix, htail] using hsplit

/-- Prefix plus outside-cutoff tail is bounded by the completed target energy. -/
theorem concrete_l2_prefix_plus_tail_le_completed_target :
    concreteL2PrefixPlusTailLeCompletedTarget := by
  intro x N
  exact le_of_eq (concrete_l2_prefix_plus_tail_eq_completed_target x N)

/-- The precise graph-norm finite-support density target follows. -/
theorem concrete_l2_precise_density_from_prefix_plus_tail_proof :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_precise_density_of_prefix_plus_tail
    concrete_l2_prefix_plus_tail_le_completed_target

end

end MathlibAnalytic
end MGAP4D
