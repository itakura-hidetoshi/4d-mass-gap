import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathSweepNormalizationAudit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A scaling-correct sweep contraction certificate for the unnormalized
finite Wilson heat-bath generator `sum_e Q_e`.

Unlike the obsolete unit-scale certificate, the coercive coefficient is
`sweepScale * (1 - contractionRate)`.  For the normalized random-scan sweep the
natural scale is the number of lattice links. -/
structure FiniteLatticeWilsonScaledHeatBathSweepContractionData
    (L : FiniteLatticeWilsonSystem) where
  sweep : (L.Configuration → ℝ) → (L.Configuration → ℝ)
  sweepScale : ℝ
  sweepScale_nonneg : 0 ≤ sweepScale
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  scaled_variance_decomposition :
    ∀ f : L.Configuration → ℝ,
      sweepScale * L.gibbsVarianceReal f ≤
        L.singleLinkHeatBathDirichletForm f +
          sweepScale * L.gibbsVarianceReal (sweep f)
  sweep_variance_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal (sweep f) ≤
        contractionRate * L.gibbsVarianceReal f
  exactGap_le_scaled_one_sub_rate :
    exactGapValueReal ≤ sweepScale * (1 - contractionRate)

/-- The scaled variance decomposition and sweep contraction imply coercivity
with coefficient `sweepScale * (1 - contractionRate)`. -/
theorem finite_lattice_scaled_one_sub_sweepRate_mul_variance_le_dirichlet
    (L : FiniteLatticeWilsonSystem)
    (S : FiniteLatticeWilsonScaledHeatBathSweepContractionData L)
    (f : L.Configuration → ℝ) :
    (S.sweepScale * (1 - S.contractionRate)) *
        L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f := by
  have hScaledContraction :
      S.sweepScale * L.gibbsVarianceReal (S.sweep f) ≤
        S.sweepScale *
          (S.contractionRate * L.gibbsVarianceReal f) :=
    mul_le_mul_of_nonneg_left
      (S.sweep_variance_contraction f) S.sweepScale_nonneg
  calc
    (S.sweepScale * (1 - S.contractionRate)) *
        L.gibbsVarianceReal f =
      S.sweepScale * L.gibbsVarianceReal f -
        S.sweepScale *
          (S.contractionRate * L.gibbsVarianceReal f) := by
      ring
    _ ≤ S.sweepScale * L.gibbsVarianceReal f -
        S.sweepScale * L.gibbsVarianceReal (S.sweep f) :=
      sub_le_sub_left hScaledContraction
        (S.sweepScale * L.gibbsVarianceReal f)
    _ ≤ L.singleLinkHeatBathDirichletForm f :=
      (sub_le_iff_le_add).2 (S.scaled_variance_decomposition f)

/-- A scaling-correct sweep certificate generates the exact-gap finite Wilson
heat-bath Poincare inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_scaledSweepContraction
    (L : FiniteLatticeWilsonSystem)
    (S : FiniteLatticeWilsonScaledHeatBathSweepContractionData L) :
    L.ExactGapSingleLinkHeatBathPoincare := by
  intro f
  calc
    exactGapValueReal * L.gibbsVarianceReal f ≤
        (S.sweepScale * (1 - S.contractionRate)) *
          L.gibbsVarianceReal f :=
      mul_le_mul_of_nonneg_right
        S.exactGap_le_scaled_one_sub_rate
        (finite_lattice_gibbsVarianceReal_nonneg L f)
    _ ≤ L.singleLinkHeatBathDirichletForm f :=
      finite_lattice_scaled_one_sub_sweepRate_mul_variance_le_dirichlet
        L S f

/-- A scaling-correct contraction certificate for the normalized concrete
random-scan heat-bath sweep.  The missing scale in the obsolete certificate is
now explicitly the number of lattice links. -/
structure FiniteLatticeWilsonScaledRandomScanHeatBathContractionData
    (L : FiniteLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  scaled_variance_decomposition :
    ∀ f : L.Configuration → ℝ,
      (Fintype.card L.Edge : ℝ) * L.gibbsVarianceReal f ≤
        L.singleLinkHeatBathDirichletForm f +
          (Fintype.card L.Edge : ℝ) *
            L.gibbsVarianceReal (L.randomScanHeatBathSweep f)
  randomScan_variance_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsVarianceReal (L.randomScanHeatBathSweep f) ≤
        contractionRate * L.gibbsVarianceReal f
  exactGap_le_edgeCard_mul_one_sub_rate :
    exactGapValueReal ≤
      (Fintype.card L.Edge : ℝ) * (1 - contractionRate)

/-- Forget the concrete random-scan form while retaining the correct link-count
normalization. -/
noncomputable def
    FiniteLatticeWilsonScaledRandomScanHeatBathContractionData.toScaledSweepData
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonScaledRandomScanHeatBathContractionData L) :
    FiniteLatticeWilsonScaledHeatBathSweepContractionData L :=
  { sweep := L.randomScanHeatBathSweep
    sweepScale := (Fintype.card L.Edge : ℝ)
    sweepScale_nonneg := Nat.cast_nonneg _
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    scaled_variance_decomposition := R.scaled_variance_decomposition
    sweep_variance_contraction := R.randomScan_variance_contraction
    exactGap_le_scaled_one_sub_rate :=
      R.exactGap_le_edgeCard_mul_one_sub_rate }

/-- A correctly normalized random-scan contraction certificate implies the
finite exact-gap heat-bath Poincare inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_scaledRandomScanContraction
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonScaledRandomScanHeatBathContractionData L) :
    L.ExactGapSingleLinkHeatBathPoincare :=
  finite_lattice_exactGap_heatBathPoincare_of_scaledSweepContraction
    L R.toScaledSweepData

/-- Uniform scaling-correct random-scan contraction data for a finite Wilson
approximation family. -/
structure FiniteLatticeWilsonApproximationFamily.UniformScaledRandomScanHeatBathContractionData
    (F : FiniteLatticeWilsonApproximationFamily) where
  edgeCard_pos : ∀ i : F.index, 0 < Fintype.card (F.system i).Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  scaled_variance_decomposition :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (Fintype.card (F.system i).Edge : ℝ) *
          (F.system i).gibbsVarianceReal f ≤
        (F.system i).singleLinkHeatBathDirichletForm f +
          (Fintype.card (F.system i).Edge : ℝ) *
            (F.system i).gibbsVarianceReal
              ((F.system i).randomScanHeatBathSweep f)
  randomScan_variance_contraction :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsVarianceReal
          ((F.system i).randomScanHeatBathSweep f) ≤
        contractionRate * (F.system i).gibbsVarianceReal f
  exactGap_le_edgeCard_mul_one_sub_rate :
    ∀ i : F.index,
      exactGapValueReal ≤
        (Fintype.card (F.system i).Edge : ℝ) *
          (1 - contractionRate)

/-- Specialize uniform scaling-correct random-scan data to one finite Wilson
system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformScaledRandomScanHeatBathContractionData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (R : F.UniformScaledRandomScanHeatBathContractionData)
    (i : F.index) :
    FiniteLatticeWilsonScaledRandomScanHeatBathContractionData (F.system i) :=
  { edgeCard_pos := R.edgeCard_pos i
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    scaled_variance_decomposition :=
      R.scaled_variance_decomposition i
    randomScan_variance_contraction :=
      R.randomScan_variance_contraction i
    exactGap_le_edgeCard_mul_one_sub_rate :=
      R.exactGap_le_edgeCard_mul_one_sub_rate i }

/-- Uniform correctly normalized random-scan contraction implies the family-wide
exact-gap heat-bath Poincare property. -/
theorem finite_lattice_uniform_exactGap_heatBathPoincare_of_scaledRandomScanContraction
    (F : FiniteLatticeWilsonApproximationFamily)
    (R : F.UniformScaledRandomScanHeatBathContractionData) :
    F.UniformExactGapSingleLinkHeatBathPoincare := by
  intro i
  exact
    finite_lattice_exactGap_heatBathPoincare_of_scaledRandomScanContraction
      (F.system i) (R.toSystemData i)

end

end MathlibAnalytic
end MGAP4D
