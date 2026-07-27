import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathPrefixConsistency
import MGAP4D.MathlibAnalytic.KolmogorovStandardBorelExtension
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Finset MeasureTheory Preorder
open scoped ENNReal

noncomputable section

/-- The canonical equivalence between an `n + 1` tuple and a path indexed by
natural times at most `n`. -/
def linearMarkovFinIicPathEquiv
    {Ω : Type*}
    (n : ℕ) :
    (Fin (n + 1) → Ω) ≃ (Finset.Iic n → Ω) where
  toFun path i :=
    path ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩
  invFun path i :=
    path ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  left_inv path := by
    funext i
    rfl
  right_inv path := by
    funext i
    cases i
    rfl

/-- Restrict an `Iic (m + k)`-indexed path to its first `m + 1` coordinates. -/
def linearMarkovIicPathPrefix
    {Ω : Type*}
    (m k : ℕ) :
    (Finset.Iic (m + k) → Ω) → (Finset.Iic m → Ω) :=
  fun path i => path ⟨i.1, by
    apply Finset.mem_Iic.mpr
    exact (Finset.mem_Iic.mp i.2).trans (Nat.le_add_right m k)⟩

/-- The `Iic` prefix map is exactly the transport of the finite-tuple prefix map
through the canonical `Fin`/`Iic` equivalences. -/
theorem linearMarkovIicPathPrefix_comp_equiv
    {Ω : Type*}
    (m k : ℕ) :
    linearMarkovIicPathPrefix (Ω := Ω) m k ∘
        linearMarkovFinIicPathEquiv (Ω := Ω) (m + k) =
      linearMarkovFinIicPathEquiv (Ω := Ω) m ∘
        linearMarkovFinitePathPrefix m k := by
  funext path i
  rfl

/-- The finite Markov path PMF transported from `Fin (n + 1)` coordinates to
Mathlib's natural prefix type `Iic n`. -/
def linearMarkovFiniteIicPathPMF
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) : PMF (Finset.Iic n → Ω) :=
  (linearMarkovFinitePathPMF initial transition n).map
    (linearMarkovFinIicPathEquiv n)

/-- The `Iic`-indexed finite path PMFs are exactly consistent under deletion of
any finite terminal block. -/
theorem linearMarkovFiniteIicPathPMF_map_prefix
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (m k : ℕ) :
    (linearMarkovFiniteIicPathPMF initial transition (m + k)).map
        (linearMarkovIicPathPrefix m k) =
      linearMarkovFiniteIicPathPMF initial transition m := by
  unfold linearMarkovFiniteIicPathPMF
  calc
    ((linearMarkovFinitePathPMF initial transition (m + k)).map
        (linearMarkovFinIicPathEquiv (m + k))).map
        (linearMarkovIicPathPrefix m k) =
      (linearMarkovFinitePathPMF initial transition (m + k)).map
        (linearMarkovIicPathPrefix m k ∘
          linearMarkovFinIicPathEquiv (m + k)) := by
            rw [PMF.map_comp]
    _ =
      (linearMarkovFinitePathPMF initial transition (m + k)).map
        (linearMarkovFinIicPathEquiv m ∘
          linearMarkovFinitePathPrefix m k) := by
            rw [linearMarkovIicPathPrefix_comp_equiv]
    _ =
      ((linearMarkovFinitePathPMF initial transition (m + k)).map
        (linearMarkovFinitePathPrefix m k)).map
          (linearMarkovFinIicPathEquiv m) := by
            rw [PMF.map_comp]
    _ =
      (linearMarkovFinitePathPMF initial transition m).map
        (linearMarkovFinIicPathEquiv m) := by
          rw [linearMarkovFinitePathPMF_map_prefix]

/-- Arbitrary ordered natural prefixes of the transported finite path PMFs are
consistent. -/
theorem linearMarkovFiniteIicPathPMF_map_frestrictLe₂
    {Ω : Type*}
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (a b : ℕ)
    (hab : a ≤ b) :
    (linearMarkovFiniteIicPathPMF initial transition b).map
        (frestrictLe₂ (α := ℕ) (π := fun _ : ℕ => Ω) hab) =
      linearMarkovFiniteIicPathPMF initial transition a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  convert linearMarkovFiniteIicPathPMF_map_prefix
    initial transition a k using 1
  funext path i
  rfl

/-- The finite-prefix probability measure obtained from the honest finite path
PMF. -/
def linearMarkovFiniteIicPathMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) : Measure (Finset.Iic n → Ω) :=
  (linearMarkovFiniteIicPathPMF initial transition n).toMeasure

instance linearMarkovFiniteIicPathMeasure_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    IsProbabilityMeasure
      (linearMarkovFiniteIicPathMeasure initial transition n) := by
  unfold linearMarkovFiniteIicPathMeasure
  infer_instance

/-- Prefix consistency after transporting the finite PMFs to probability
measures. -/
theorem linearMarkovFiniteIicPathMeasure_map_frestrictLe₂
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (a b : ℕ)
    (hab : a ≤ b) :
    (linearMarkovFiniteIicPathMeasure initial transition b).map
        (frestrictLe₂ (α := ℕ) (π := fun _ : ℕ => Ω) hab) =
      linearMarkovFiniteIicPathMeasure initial transition a := by
  unfold linearMarkovFiniteIicPathMeasure
  calc
    (linearMarkovFiniteIicPathPMF initial transition b).toMeasure.map
        (frestrictLe₂ (α := ℕ) (π := fun _ : ℕ => Ω) hab) =
      ((linearMarkovFiniteIicPathPMF initial transition b).map
        (frestrictLe₂ (α := ℕ) (π := fun _ : ℕ => Ω) hab)).toMeasure :=
          PMF.toMeasure_map _
            (measurable_frestrictLe₂
              (α := ℕ) (π := fun _ : ℕ => Ω) hab)
    _ = (linearMarkovFiniteIicPathPMF initial transition a).toMeasure :=
      congrArg PMF.toMeasure
        (linearMarkovFiniteIicPathPMF_map_frestrictLe₂
          initial transition a b hab)

/-- The full finite-dimensional projective family generated from the natural
prefix laws. -/
def linearMarkovFinitePathProjectiveFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (J : Finset ℕ) : Measure (J → Ω) :=
  MeasureTheory.inducedFamily
    (X := fun _ : ℕ => Ω)
    (linearMarkovFiniteIicPathMeasure initial transition) J

instance linearMarkovFinitePathProjectiveFamily_isProbabilityMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (J : Finset ℕ) :
    IsProbabilityMeasure
      (linearMarkovFinitePathProjectiveFamily initial transition J) := by
  unfold linearMarkovFinitePathProjectiveFamily
  infer_instance

/-- The induced finite-dimensional family is a genuine Mathlib projective
measure family. -/
theorem linearMarkovFinitePathProjectiveFamily_projective
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) :
    IsProjectiveMeasureFamily
      (α := fun _ : ℕ => Ω)
      (linearMarkovFinitePathProjectiveFamily initial transition) := by
  exact MeasureTheory.isProjectiveMeasureFamily_inducedFamily
    (X := fun _ : ℕ => Ω) _
    (fun a b hab =>
      linearMarkovFiniteIicPathMeasure_map_frestrictLe₂
        initial transition a b hab)

/-- The infinite Markov path probability measure produced by the standard-Borel
Kolmogorov extension of the honest finite path laws. -/
def linearMarkovInfinitePathMeasure
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) :
    Measure (ℕ → Ω) :=
  standardBorelKolmogorovProjectiveLimit
    (α := fun _ : ℕ => Ω)
    (linearMarkovFinitePathProjectiveFamily initial transition)
    (linearMarkovFinitePathProjectiveFamily_projective initial transition)

instance linearMarkovInfinitePathMeasure_isProbabilityMeasure
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω) :
    IsProbabilityMeasure
      (linearMarkovInfinitePathMeasure initial transition) := by
  unfold linearMarkovInfinitePathMeasure
  exact standardBorelKolmogorovProjectiveLimit_probability
    (linearMarkovFinitePathProjectiveFamily_projective initial transition)

/-- Every initial natural prefix of the infinite path measure is the prescribed
finite path probability measure. -/
theorem linearMarkovInfinitePathMeasure_map_frestrictLe
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovInfinitePathMeasure initial transition).map
        (frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n) =
      linearMarkovFiniteIicPathMeasure initial transition n := by
  let P := linearMarkovFinitePathProjectiveFamily initial transition
  have hP :
      IsProjectiveMeasureFamily (α := fun _ : ℕ => Ω) P :=
    linearMarkovFinitePathProjectiveFamily_projective initial transition
  change
    (standardBorelKolmogorovProjectiveLimit
      (α := fun _ : ℕ => Ω) P hP).map
        (frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n) =
      linearMarkovFiniteIicPathMeasure initial transition n
  have hLimit :
      IsProjectiveLimit
        (standardBorelKolmogorovProjectiveLimit
          (α := fun _ : ℕ => Ω) P hP) P :=
    isProjectiveLimit_standardBorelKolmogorovProjectiveLimit hP
  have hn :=
    (MeasureTheory.isProjectiveLimit_nat_iff
      (X := fun _ : ℕ => Ω) hP _).mp hLimit n
  calc
    (standardBorelKolmogorovProjectiveLimit
        (α := fun _ : ℕ => Ω) P hP).map
        (frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n) =
      P (Finset.Iic n) := hn
    _ = linearMarkovFiniteIicPathMeasure initial transition n := by
      unfold P linearMarkovFinitePathProjectiveFamily
      exact MeasureTheory.inducedFamily_Iic
        (X := fun _ : ℕ => Ω)
        (linearMarkovFiniteIicPathMeasure initial transition) n

/-- Restrict an infinite path to its first `n + 1` coordinates in the original
`Fin` tuple representation. -/
def linearMarkovInfinitePathFinPrefix
    {Ω : Type*}
    (n : ℕ) :
    (ℕ → Ω) → (Fin (n + 1) → Ω) :=
  fun path i => path i.1

/-- The finite-tuple prefix map is measurable. -/
theorem measurable_linearMarkovInfinitePathFinPrefix
    {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) :
    Measurable (linearMarkovInfinitePathFinPrefix (Ω := Ω) n) := by
  unfold linearMarkovInfinitePathFinPrefix
  fun_prop

/-- Every original `Fin`-indexed finite path PMF is recovered exactly as a
marginal of the infinite path probability measure. -/
theorem linearMarkovInfinitePathMeasure_map_finPrefix
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ) :
    (linearMarkovInfinitePathMeasure initial transition).map
        (linearMarkovInfinitePathFinPrefix n) =
      (linearMarkovFinitePathPMF initial transition n).toMeasure := by
  have hPrefix :
      linearMarkovInfinitePathFinPrefix (Ω := Ω) n =
        (linearMarkovFinIicPathEquiv (Ω := Ω) n).symm ∘
          frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n := by
    funext path i
    rfl
  have hEquivMeasurable :
      Measurable (linearMarkovFinIicPathEquiv (Ω := Ω) n).symm :=
    measurable_of_finite _
  rw [hPrefix]
  calc
    (linearMarkovInfinitePathMeasure initial transition).map
        ((linearMarkovFinIicPathEquiv n).symm ∘
          frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n) =
      ((linearMarkovInfinitePathMeasure initial transition).map
        (frestrictLe (α := ℕ) (π := fun _ : ℕ => Ω) n)).map
          (linearMarkovFinIicPathEquiv n).symm := by
            symm
            exact Measure.map_map hEquivMeasurable
              (measurable_frestrictLe
                (α := ℕ) (π := fun _ : ℕ => Ω) n)
    _ = (linearMarkovFiniteIicPathMeasure initial transition n).map
        (linearMarkovFinIicPathEquiv n).symm := by
          rw [linearMarkovInfinitePathMeasure_map_frestrictLe]
    _ = ((linearMarkovFiniteIicPathPMF initial transition n).map
        (linearMarkovFinIicPathEquiv n).symm).toMeasure := by
          unfold linearMarkovFiniteIicPathMeasure
          exact PMF.toMeasure_map _ hEquivMeasurable
    _ = (linearMarkovFinitePathPMF initial transition n).toMeasure := by
      congr 1
      unfold linearMarkovFiniteIicPathPMF
      rw [PMF.map_comp]
      simpa [Function.comp_def] using
        PMF.map_id (linearMarkovFinitePathPMF initial transition n)

/-- Under expectation stationarity, every coordinate of the infinite Markov
path has the initial probability law. -/
theorem linearMarkovInfinitePathMeasure_map_eval_of_expectation_stationary
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (hstationary : ∀ f : Ω → ℝ,
      finitePMFExpectationReal initial
          (fun x => finitePMFExpectationReal (transition x) f) =
        finitePMFExpectationReal initial f)
    (i : ℕ) :
    (linearMarkovInfinitePathMeasure initial transition).map
        (fun path => path i) =
      initial.toMeasure := by
  have hEval :
      (fun path : ℕ → Ω => path i) =
        (fun path : Fin (i + 1) → Ω => path (Fin.last i)) ∘
          linearMarkovInfinitePathFinPrefix i := by
    funext path
    rfl
  have hPrefixMeasurable :
      Measurable (linearMarkovInfinitePathFinPrefix (Ω := Ω) i) :=
    measurable_linearMarkovInfinitePathFinPrefix i
  have hEvalMeasurable :
      Measurable (fun path : Fin (i + 1) → Ω => path (Fin.last i)) :=
    measurable_of_finite _
  rw [hEval]
  calc
    (linearMarkovInfinitePathMeasure initial transition).map
        ((fun path : Fin (i + 1) → Ω => path (Fin.last i)) ∘
          linearMarkovInfinitePathFinPrefix i) =
      ((linearMarkovInfinitePathMeasure initial transition).map
        (linearMarkovInfinitePathFinPrefix i)).map
          (fun path => path (Fin.last i)) := by
            symm
            exact Measure.map_map hEvalMeasurable hPrefixMeasurable
    _ = (linearMarkovFinitePathPMF initial transition i).toMeasure.map
        (fun path => path (Fin.last i)) := by
          rw [linearMarkovInfinitePathMeasure_map_finPrefix]
    _ = ((linearMarkovFinitePathPMF initial transition i).map
        (fun path => path (Fin.last i))).toMeasure :=
          PMF.toMeasure_map _ hEvalMeasurable
    _ = initial.toMeasure :=
      congrArg PMF.toMeasure
        (linearMarkovFinitePathPMF_map_last_of_expectation_stationary
          initial transition hstationary i)

end

end MathlibAnalytic
end MGAP4D
