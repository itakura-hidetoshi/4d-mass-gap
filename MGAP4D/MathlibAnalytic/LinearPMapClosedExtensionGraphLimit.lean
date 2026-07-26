import MGAP4D.MathlibAnalytic.LinearPMapDomainPointOfLE
import Mathlib.Topology.Sequences

namespace LinearPMap

noncomputable section

open Filter Set Topology

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A B : E →ₗ.[ℝ] E}

/-- A strongly convergent graph sequence for an operator lies in every closed
extension at its limiting graph point.

The sequence is taken in the domain of `A`; `A ≤ B` transports each graph point
to `B`. Closedness of `B` then puts the pair of strong limits in the graph of
`B`. -/
theorem mem_graph_of_tendsto_of_isClosed_extension
    (hAB : A ≤ B)
    (hB : B.IsClosed)
    {u : ℕ → A.domain}
    {x y : E}
    (hx : Tendsto (fun n => ((u n : A.domain) : E)) atTop (nhds x))
    (hy : Tendsto (fun n => A (u n)) atTop (nhds y)) :
    (x, y) ∈ B.graph := by
  have hx' :
      Tendsto
        (fun n => ((domainPointOfLE hAB (u n) : B.domain) : E))
        atTop (nhds x) := by
    simpa only [coe_domainPointOfLE] using hx
  have hy' :
      Tendsto
        (fun n => B (domainPointOfLE hAB (u n)))
        atTop (nhds y) := by
    simpa only [apply_domainPointOfLE] using hy
  have hpair :
      Tendsto
        (fun n =>
          (((domainPointOfLE hAB (u n) : B.domain) : E),
            B (domainPointOfLE hAB (u n))))
        atTop (nhds (x, y)) :=
    hx'.prodMk_nhds hy'
  have hClosedGraph : IsClosed (B.graph : Set (E × E)) := hB
  exact hClosedGraph.isSeqClosed
    (fun n => B.mem_graph (domainPointOfLE hAB (u n))) hpair

/-- The limiting base vector, bundled in the domain of a closed graph
extension. -/
noncomputable def domainPointOfClosedExtensionGraphLimit
    (hAB : A ≤ B)
    (hB : B.IsClosed)
    {u : ℕ → A.domain}
    {x y : E}
    (hx : Tendsto (fun n => ((u n : A.domain) : E)) atTop (nhds x))
    (hy : Tendsto (fun n => A (u n)) atTop (nhds y)) :
    B.domain :=
  ⟨x, B.mem_domain_of_mem_graph
    (mem_graph_of_tendsto_of_isClosed_extension hAB hB hx hy)⟩

@[simp] theorem coe_domainPointOfClosedExtensionGraphLimit
    (hAB : A ≤ B)
    (hB : B.IsClosed)
    {u : ℕ → A.domain}
    {x y : E}
    (hx : Tendsto (fun n => ((u n : A.domain) : E)) atTop (nhds x))
    (hy : Tendsto (fun n => A (u n)) atTop (nhds y)) :
    ((domainPointOfClosedExtensionGraphLimit hAB hB hx hy : B.domain) : E) = x :=
  rfl

/-- The closed extension takes the graph-limit base vector to the graph-limit
operator value. -/
theorem apply_domainPointOfClosedExtensionGraphLimit
    (hAB : A ≤ B)
    (hB : B.IsClosed)
    {u : ℕ → A.domain}
    {x y : E}
    (hx : Tendsto (fun n => ((u n : A.domain) : E)) atTop (nhds x))
    (hy : Tendsto (fun n => A (u n)) atTop (nhds y)) :
    B (domainPointOfClosedExtensionGraphLimit hAB hB hx hy) = y := by
  exact B.mem_graph_snd_inj
    (B.mem_graph (domainPointOfClosedExtensionGraphLimit hAB hB hx hy))
    (mem_graph_of_tendsto_of_isClosed_extension hAB hB hx hy)
    rfl

end

end LinearPMap
