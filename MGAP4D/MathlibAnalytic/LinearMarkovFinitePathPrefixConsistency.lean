import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPMF
import MGAP4D.MathlibAnalytic.LinearMarkovCylinderMoment
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Restrict an `(m + k)`-transition path to its first `m + 1` coordinates.
The natural number `k` is the number of terminal coordinates discarded. -/
def linearMarkovFinitePathPrefix
    {Ω : Type*}
    (m k : ℕ) :
    (Fin (m + k + 1) → Ω) → (Fin (m + 1) → Ω) :=
  fun path i => path ⟨i.1, by omega⟩

@[simp] theorem linearMarkovFinitePathPrefix_zero
    {Ω : Type*}
    (m : ℕ) :
    linearMarkovFinitePathPrefix (Ω := Ω) m 0 = id := by
  funext path
  funext i
  rfl

/-- Restricting after deleting one terminal coordinate is the same as directly
restricting while discarding one additional terminal coordinate. -/
theorem linearMarkovFinitePathPrefix_succ
    {Ω : Type*}
    (m k : ℕ) :
    linearMarkovFinitePathPrefix (Ω := Ω) m (k + 1) =
      linearMarkovFinitePathPrefix (Ω := Ω) m k ∘ Fin.init := by
  funext path
  funext i
  rfl

/-- The arbitrary finite Markov path PMFs form an exactly projectively
consistent family for every pair of prefix horizons. -/
theorem linearMarkovFinitePathPMF_map_prefix
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m k : ℕ) :
    (linearMarkovFinitePathPMF initial transition (m + k)).map
        (linearMarkovFinitePathPrefix m k) =
      linearMarkovFinitePathPMF initial transition m := by
  induction k with
  | zero =>
      simp only [Nat.add_zero, linearMarkovFinitePathPrefix_zero]
      exact PMF.map_id _
  | succ k ih =>
      rw [Nat.add_succ]
      calc
        (linearMarkovFinitePathPMF initial transition ((m + k) + 1)).map
            (linearMarkovFinitePathPrefix m (k + 1)) =
          ((linearMarkovFinitePathPMF initial transition ((m + k) + 1)).map
              Fin.init).map
            (linearMarkovFinitePathPrefix m k) := by
              rw [PMF.map_comp]
              congr 1
              exact linearMarkovFinitePathPrefix_succ m k
        _ =
          (linearMarkovFinitePathPMF initial transition (m + k)).map
              (linearMarkovFinitePathPrefix m k) := by
                rw [linearMarkovFinitePathPMF_succ_map_init]
        _ = linearMarkovFinitePathPMF initial transition m := ih

/-- Appending any finite number of unobserved terminal coordinates, represented
by constant-one observables, leaves a finite-cylinder moment unchanged. -/
theorem linearMarkovCylinderMoment_append_replicate_one
    {Ω : Type*}
    (state : (Ω → ℝ) → ℝ)
    (P : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ))
    (hPone : P (fun _ : Ω => (1 : ℝ)) = fun _ => 1)
    (fs : List (Ω → ℝ))
    (k : ℕ) :
    linearMarkovCylinderMoment state P
        (fs ++ List.replicate k (fun _ : Ω => (1 : ℝ))) =
      linearMarkovCylinderMoment state P fs := by
  induction k generalizing fs with
  | zero =>
      simp
  | succ k ih =>
      rw [List.replicate_succ, ← List.append_assoc]
      rw [ih (fs := fs ++ [fun _ : Ω => (1 : ℝ)])]
      exact linearMarkovCylinderMoment_append_one state P hPone fs

end

end MathlibAnalytic
end MGAP4D
