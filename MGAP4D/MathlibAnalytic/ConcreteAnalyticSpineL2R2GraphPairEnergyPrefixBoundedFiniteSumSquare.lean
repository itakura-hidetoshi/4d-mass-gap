import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedFiniteSumAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

theorem concrete_l2_graph_pair_prefix_sum_sq_add_expansion
    (N : Nat) (a b : Nat -> Real) :
    (Finset.range N).sum (fun n => (a n + b n) ^ 2) =
      (Finset.range N).sum (fun n => a n ^ 2) +
        (Finset.range N).sum (fun n => a n * b n) * 2 +
          (Finset.range N).sum (fun n => b n ^ 2) := by
  calc
    (Finset.range N).sum (fun n => (a n + b n) ^ 2)
        = (Finset.range N).sum (fun n => a n * b n * 2 + a n ^ 2 + b n ^ 2) := by
          exact Finset.sum_congr rfl (fun n _hn => by ring)
    _ = (Finset.range N).sum (fun n => a n ^ 2) +
        (Finset.range N).sum (fun n => a n * b n) * 2 +
          (Finset.range N).sum (fun n => b n ^ 2) := by
          simpa only [Finset.sum_attach] using
            concrete_l2_graph_pair_prefix_sum_mixed_sq_expansion N a b

end

end MathlibAnalytic
end MGAP4D
