import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonRandomScanHeatBathSweep

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Because the public exact gap is strictly above one, it cannot be bounded by
`1 - ρ` for any nonnegative contraction rate `ρ`.  This isolates the
normalization mismatch in the old sweep certificate. -/
theorem exactGapValueReal_not_le_one_sub_of_nonneg
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ¬ exactGapValueReal ≤ 1 - ρ := by
  intro hGap
  have hGap_le_one : exactGapValueReal ≤ 1 :=
    le_trans hGap (sub_le_self 1 hρ)
  exact (not_le_of_gt exactGapValueReal_above_one) hGap_le_one

/-- The original unscaled one-sweep contraction structure is uninhabited.
Its fields require simultaneously `ρ ≥ 0`, `Δ > 1`, and `Δ ≤ 1 - ρ`. -/
theorem finite_lattice_heatBathSweepContractionData_isEmpty
    (L : FiniteLatticeWilsonSystem) :
    IsEmpty (FiniteLatticeWilsonHeatBathSweepContractionData L) :=
  ⟨fun S =>
    (exactGapValueReal_not_le_one_sub_of_nonneg
      S.contractionRate_nonneg) S.exactGap_le_one_sub_rate⟩

/-- The same normalization contradiction makes the concrete random-scan
certificate uninhabited. -/
theorem finite_lattice_randomScanHeatBathContractionData_isEmpty
    (L : FiniteLatticeWilsonSystem) :
    IsEmpty (FiniteLatticeWilsonRandomScanHeatBathContractionData L) :=
  ⟨fun R =>
    (exactGapValueReal_not_le_one_sub_of_nonneg
      R.contractionRate_nonneg) R.exactGap_le_one_sub_rate⟩

/-- No family-wide unscaled sweep certificate can exist either. -/
theorem finite_lattice_uniformHeatBathSweepContractionData_isEmpty
    (F : FiniteLatticeWilsonApproximationFamily) :
    IsEmpty F.UniformHeatBathSweepContractionData :=
  ⟨fun S =>
    (exactGapValueReal_not_le_one_sub_of_nonneg
      S.contractionRate_nonneg) S.exactGap_le_one_sub_rate⟩

/-- No family-wide unscaled random-scan certificate can exist either. -/
theorem finite_lattice_uniformRandomScanHeatBathContractionData_isEmpty
    (F : FiniteLatticeWilsonApproximationFamily) :
    IsEmpty F.UniformRandomScanHeatBathContractionData :=
  ⟨fun R =>
    (exactGapValueReal_not_le_one_sub_of_nonneg
      R.contractionRate_nonneg) R.exactGap_le_one_sub_rate⟩

end

end MathlibAnalytic
end MGAP4D
