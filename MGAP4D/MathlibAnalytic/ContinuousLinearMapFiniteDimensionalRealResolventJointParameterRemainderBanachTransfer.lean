import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalZeroFreeCharacteristicCalculusCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The finite-dimensional input space carrying a base resolvent family, an
endpoint resolvent family, and the complete finite operator-direction family. -/
abbrev ContinuousLinearMapJointTaylorDysonRemainderInput
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (taylorOrder m : ℕ) :=
  ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
    (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
      (Fin m → (V →L[ℝ] V))

/-- Constructor for the complete remainder input. -/
def continuousLinearMapJointTaylorDysonRemainderInput
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {taylorOrder m : ℕ}
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (H : Fin m → (V →L[ℝ] V)) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m :=
  ((Rbase, Rend), H)

noncomputable instance continuousLinearMapJointTaylorDysonRemainderInputCompleteSpace
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (taylorOrder m : ℕ) :
    CompleteSpace
      (ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m) :=
  inferInstance

/-- Componentwise uniform convergence of the two resolvent families and
ordinary convergence of the finite direction family combine into uniform
convergence in the complete finite-dimensional input norm. -/
theorem continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
    {α ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} {s : Set ι} {taylorOrder m : ℕ}
    (Rbase : α → ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rbase0 : ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rend : α → ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rend0 : ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hbase : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖Rbase a i - Rbase0 i‖ < eta)
    (hend : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖Rend a i - Rend0 i‖ < eta)
    (hH : Tendsto H l (𝓝 H0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderInput
          (Rbase a i) (Rend a i) (H a) -
        continuousLinearMapJointTaylorDysonRemainderInput
          (Rbase0 i) (Rend0 i) H0‖ < eta := by
  intro eta heta
  have hHeta : ∀ᶠ a in l, ‖H a - H0‖ < eta := by
    rw [Metric.tendsto_nhds] at hH
    simpa [dist_eq_norm] using hH eta heta
  filter_upwards [hbase eta heta, hend eta heta, hHeta] with a ha hb hc
  intro i hi
  rw [← dist_eq_norm]
  simpa [continuousLinearMapJointTaylorDysonRemainderInput,
    Prod.dist_eq, dist_eq_norm, max_lt_iff] using
    And.intro (And.intro (ha i hi) (hb i hi)) hc

/-- A jointly continuous finite-dimensional remainder observable transfers
uniform convergence of complete remainder inputs to uniform convergence in the
actual remainder-rectangle Banach norm. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  intro epsilon hepsilon
  let Phi := fun x : ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m => fun _p : PUnit =>
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m x.2 ds h x.1.1 x.1.2
  have hPhi : Continuous (fun p :
      (ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m) × PUnit =>
      Phi p.1 p.2) :=
    (continuous_continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      (V := V) baseOrder taylorOrder tailOrder m ds h).comp continuous_fst
  have htransfer :=
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
      X X0 Phi hPhi R hR hX0 hX ({PUnit.unit} : Set PUnit)
        isCompact_singleton epsilon hepsilon
  filter_upwards [htransfer] with a ha
  intro i hi
  simpa [Phi] using ha i hi PUnit.unit (by simp)

/-- The same complete-input transfer holds for every arbitrary Banach-valued
continuous-linear observation of the exact remainder rectangle. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
    {α ι V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {l : Filter α} {s : Set ι}
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  intro epsilon hepsilon
  let Phi := fun x : ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m => fun _p : PUnit =>
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder taylorOrder tailOrder m x.2 ds h x.1.1 x.1.2
  have hPhi : Continuous (fun p :
      (ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m) × PUnit =>
      Phi p.1 p.2) :=
    (continuous_continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder taylorOrder tailOrder m ds h).comp continuous_fst
  have htransfer :=
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
      X X0 Phi hPhi R hR hX0 hX ({PUnit.unit} : Set PUnit)
        isCompact_singleton epsilon hepsilon
  filter_upwards [htransfer] with a ha
  intro i hi
  simpa [Phi] using ha i hi PUnit.unit (by simp)

/-- Basis-independent traces inherit the complete finite-dimensional remainder
input transfer in the true finite-product norm. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailTraceRectangularJet_tendsto_uniform
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
      (continuousLinearMapTrace (V := V)) baseOrder taylorOrder tailOrder m
      ds h X X0 R hR hX0 hX

end MathlibAnalytic
end MGAP4D
