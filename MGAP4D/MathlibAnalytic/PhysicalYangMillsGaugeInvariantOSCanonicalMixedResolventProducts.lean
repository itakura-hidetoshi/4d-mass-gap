import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace ContinuousLinearMap

variable {ι α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered composition product of a finite list of continuous linear endomorphisms. -/
def orderedProduct (A : α → E →L[ℝ] E) : List α → E →L[ℝ] E
  | [] => 1
  | a :: s => A a * orderedProduct A s

@[simp] theorem orderedProduct_apply_nil
    (A : α → E →L[ℝ] E) (x : E) :
    orderedProduct A [] x = x := rfl

@[simp] theorem orderedProduct_apply_cons
    (A : α → E →L[ℝ] E) (a : α) (s : List α) (x : E) :
    orderedProduct A (a :: s) x = A a (orderedProduct A s x) := rfl

/-- Strong convergence and separate uniform operator bounds pass to each finite
ordered product. -/
theorem tendsto_orderedProduct_apply_of_pointwise_of_uniform_opNorm_le
    (l : Filter ι)
    (A : ι → α → E →L[ℝ] E)
    (R : α → E →L[ℝ] E)
    (K : α → ℝ)
    (hA : ∀ i a, ‖A i a‖ ≤ K a)
    (hPoint : ∀ a x, Tendsto (fun i => A i a x) l (𝓝 (R a x))) :
    ∀ s : List α, ∀ x : E,
      Tendsto (fun i => orderedProduct (A i) s x) l
        (𝓝 (orderedProduct R s x)) := by
  intro s
  induction s with
  | nil =>
      intro x
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x))
  | cons a s ih =>
      intro x
      let v : E := orderedProduct R s x
      have hTail : Tendsto (fun i => orderedProduct (A i) s x) l (𝓝 v) := by
        simpa [v] using ih x
      have hDiff :
          Tendsto (fun i => orderedProduct (A i) s x - v) l (𝓝 0) := by
        simpa using hTail.sub
          (tendsto_const_nhds : Tendsto (fun _ : ι => v) l (𝓝 v))
      have hMajorant :
          Tendsto (fun i => K a * ‖orderedProduct (A i) s x - v‖) l
            (𝓝 0) := by
        have hK : Tendsto (fun _ : ι => K a) l (𝓝 (K a)) :=
          tendsto_const_nhds
        simpa using hK.mul hDiff.norm
      have hVariable :
          Tendsto (fun i => A i a (orderedProduct (A i) s x - v)) l
            (𝓝 0) := by
        apply squeeze_zero_norm'
        · exact Eventually.of_forall fun i =>
            (A i a).le_of_opNorm_le (hA i a)
              (orderedProduct (A i) s x - v)
        · exact hMajorant
      have hFixed : Tendsto (fun i => A i a v) l (𝓝 (R a v)) :=
        hPoint a v
      have hSum := hVariable.add hFixed
      simpa [v, map_sub] using hSum

end ContinuousLinearMap

end

end MathlibAnalytic
end MGAP4D
