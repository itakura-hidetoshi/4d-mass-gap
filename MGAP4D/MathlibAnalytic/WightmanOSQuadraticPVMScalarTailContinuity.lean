import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelStrongCompactTailConvergence
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The complement of the symmetric natural-number energy window `[-n,n]`. -/
def pvmNatEnergyTail (n : ℕ) : Set ℝ :=
  (pvmEnergyWindow (n : ℝ))ᶜ

/-- Natural energy tails are Borel measurable. -/
theorem measurableSet_pvmNatEnergyTail (n : ℕ) :
    MeasurableSet (pvmNatEnergyTail n) := by
  exact (measurableSet_pvmEnergyWindow (n : ℝ)).compl

/-- The natural energy tails decrease as the cutoff grows. -/
theorem antitone_pvmNatEnergyTail : Antitone pvmNatEnergyTail := by
  intro n m hnm x hx
  change x ∉ pvmEnergyWindow (m : ℝ) at hx
  change x ∉ pvmEnergyWindow (n : ℝ)
  intro hxn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  apply hx
  exact ⟨le_trans (neg_le_neg hnmR) hxn.1, le_trans hxn.2 hnmR⟩

/-- The intersection of all natural energy tails is empty. -/
theorem iInter_pvmNatEnergyTail :
    (⋂ n : ℕ, pvmNatEnergyTail n) = ∅ := by
  ext energy
  constructor
  · intro henergy
    have hAll : ∀ n : ℕ, energy ∈ pvmNatEnergyTail n :=
      Set.mem_iInter.mp henergy
    obtain ⟨n, hn⟩ := exists_nat_gt |energy|
    have hnR : |energy| < (n : ℝ) := by exact_mod_cast hn
    have hleft : -(n : ℝ) ≤ energy := by
      have hnegAbs : -|energy| ≤ energy := neg_abs_le energy
      have hnegN : -(n : ℝ) < -|energy| := neg_lt_neg hnR
      linarith
    have hright : energy ≤ (n : ℝ) :=
      le_trans (le_abs_self energy) hnR.le
    have hwindow : energy ∈ pvmEnergyWindow (n : ℝ) :=
      ⟨hleft, hright⟩
    have hfalse : False := (hAll n) hwindow
    exact hfalse.elim
  · intro henergy
    simpa using henergy

/-- The scalar spectral mass of the complements of growing finite energy
windows converges to zero for the scalar measure actually constructed from
quadratic PVM countable additivity. -/
theorem quadraticPVM_scalarMeasure_natEnergyTail_tendsto_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) :
    Tendsto
      (fun n : ℕ => A.scalarMeasure ψ (pvmNatEnergyTail n))
      atTop
      (𝓝 0) := by
  have hNullMeasurable :
      ∀ n : ℕ, NullMeasurableSet (pvmNatEnergyTail n) (A.scalarMeasure ψ) := by
    intro n
    exact (measurableSet_pvmNatEnergyTail n).nullMeasurableSet
  have hFinite :
      ∃ n : ℕ, A.scalarMeasure ψ (pvmNatEnergyTail n) ≠ ⊤ := by
    refine ⟨0, ?_⟩
    rw [quadraticPVM_scalarMeasure_apply A ψ
      (pvmNatEnergyTail 0) (measurableSet_pvmNatEnergyTail 0)]
    exact ENNReal.ofReal_ne_top
  have hMeasure :=
    tendsto_measure_iInter_atTop
      (μ := A.scalarMeasure ψ)
      hNullMeasurable antitone_pvmNatEnergyTail hFinite
  rw [iInter_pvmNatEnergyTail] at hMeasure
  simpa [Function.comp_def] using hMeasure

/-- Consequently, the ambient spectral projections of the natural energy tails
converge strongly to zero at every Hilbert vector. -/
theorem quadraticPVM_projection_natEnergyTail_tendsto_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) :
    Tendsto
      (fun n : ℕ => ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖)
      atTop
      (𝓝 0) := by
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  have hMass := quadraticPVM_scalarMeasure_natEnergyTail_tendsto_zero A ψ
  have hBound : 0 < ENNReal.ofReal (ε ^ 2) := by
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)
  have hEventuallyMass :
      ∀ᶠ n : ℕ in atTop,
        A.scalarMeasure ψ (pvmNatEnergyTail n) < ENNReal.ofReal (ε ^ 2) :=
    (tendsto_order.1 hMass).2 _ hBound
  filter_upwards [hEventuallyMass] with n hn
  rw [quadraticPVM_scalarMeasure_apply A ψ
    (pvmNatEnergyTail n) (measurableSet_pvmNatEnergyTail n)] at hn
  have hSq :
      ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε)).mp hn
  have hNormNonneg :
      0 ≤ ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ := norm_nonneg _
  have hNormLt :
      ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ < ε := by
    nlinarith
  simpa [Real.dist_eq, abs_of_nonneg hNormNonneg] using hNormLt

/-- Epsilon form of strong spectral-tail vanishing. -/
theorem quadraticPVM_projection_natEnergyTail_eventually_small
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖M.spectralPVM.projection (pvmNatEnergyTail n) ψ‖ < ε := by
  have h := quadraticPVM_projection_natEnergyTail_tendsto_zero A ψ
  have hMetric := Metric.tendsto_nhds.1 h ε hε
  filter_upwards [hMetric] with n hn
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn

end

end MathlibAnalytic
end MGAP4D
