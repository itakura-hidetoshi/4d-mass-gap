import MGAP4D.MathlibAnalytic.FiniteWilsonCanonicalHeatBathHamiltonian
import MGAP4D.MathlibAnalytic.FiniteWilsonScaledHeatBathSweepContraction

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Gibbs pairing is homogeneous in its first argument. -/
theorem finite_lattice_gibbsPairingReal_smul_left
    (L : FiniteLatticeWilsonSystem)
    (c : ℝ) (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal (c • f) g =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For a nonempty edge set, the canonical observable Hamiltonian is exactly
`|E|` times identity minus the normalized random-scan heat-bath sweep. -/
theorem finite_lattice_singleLinkHeatBathHamiltonianObservable_eq_edgeCard_sub_randomScan
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathHamiltonianObservable f =
      (Fintype.card L.Edge : ℝ) • f -
        (Fintype.card L.Edge : ℝ) • L.randomScanHeatBathSweep f := by
  classical
  funext A
  rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_apply]
  change
    (∑ e : L.Edge,
      (f A - L.singleLinkConditionalExpectation f A e)) =
      (Fintype.card L.Edge : ℝ) * f A -
        (Fintype.card L.Edge : ℝ) *
          ((Fintype.card L.Edge : ℝ)⁻¹ *
            ∑ e : L.Edge,
              L.singleLinkConditionalExpectation f A e)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  field_simp [hCard]

/-- The canonical heat-bath Dirichlet form is the exact random-scan Rayleigh
defect multiplied by the number of links. -/
theorem finite_lattice_singleLinkHeatBathDirichletForm_eq_edgeCard_mul_randomScanRayleighDefect
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm f =
      (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal f f -
          L.gibbsPairingReal (L.randomScanHeatBathSweep f) f) := by
  calc
    L.singleLinkHeatBathDirichletForm f =
        L.gibbsPairingReal
          (L.singleLinkHeatBathHamiltonianObservable f) f :=
      (finite_lattice_singleLinkHeatBathHamiltonianObservable_quadraticForm
        L f).symm
    _ = L.gibbsPairingReal
          ((Fintype.card L.Edge : ℝ) • f -
            (Fintype.card L.Edge : ℝ) •
              L.randomScanHeatBathSweep f) f := by
      rw [finite_lattice_singleLinkHeatBathHamiltonianObservable_eq_edgeCard_sub_randomScan
        L hEdge f]
    _ = (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal f f -
          L.gibbsPairingReal (L.randomScanHeatBathSweep f) f) := by
      rw [finite_lattice_gibbsPairingReal_sub_left,
        finite_lattice_gibbsPairingReal_smul_left,
        finite_lattice_gibbsPairingReal_smul_left]
      ring

/-- Gibbs centering produces a mean-zero observable. -/
theorem finite_lattice_gibbsExpectationReal_centered
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (L.gibbsCenteredObservable f) = 0 := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
    FiniteLatticeWilsonSystem.gibbsCenteredObservable
  calc
    (∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          (f A - L.gibbsExpectationReal f)) =
      (∑ A : L.Configuration,
        L.gibbsProbabilityReal A * f A) -
      (∑ A : L.Configuration,
        L.gibbsProbabilityReal A * L.gibbsExpectationReal f) := by
      rw [Finset.sum_sub_distrib]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro A _hA
        ring
      · apply Finset.sum_congr rfl
        intro A _hA
        ring
    _ = L.gibbsExpectationReal f -
        L.gibbsExpectationReal f *
          (∑ A : L.Configuration, L.gibbsProbabilityReal A) := by
      unfold FiniteLatticeWilsonSystem.gibbsExpectationReal
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ = 0 := by
      rw [finite_lattice_gibbsProbabilityReal_sum_eq_one]
      ring

/-- The Gibbs squared norm of the centered observable is the Gibbs variance. -/
theorem finite_lattice_gibbsPairingReal_centered_self
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.gibbsCenteredObservable f)
        (L.gibbsCenteredObservable f) =
      L.gibbsVarianceReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.gibbsCenteredObservable
    FiniteLatticeWilsonSystem.gibbsVarianceReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Local fluctuation projections are unchanged by Gibbs centering. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_centered
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (L.gibbsCenteredObservable f) =
      L.singleLinkHeatBathFluctuationLinearMap e f := by
  have hCentered :
      L.gibbsCenteredObservable f =
        f - L.gibbsExpectationReal f •
          (fun _ : L.Configuration => (1 : ℝ)) := by
    funext A
    simp [FiniteLatticeWilsonSystem.gibbsCenteredObservable]
  rw [hCentered, map_sub, map_smul,
    finite_lattice_singleLinkHeatBathFluctuationLinearMap_one]
  simp

/-- The heat-bath Dirichlet form is invariant under Gibbs centering. -/
theorem finite_lattice_singleLinkHeatBathDirichletForm_centered
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathDirichletForm
        (L.gibbsCenteredObservable f) =
      L.singleLinkHeatBathDirichletForm f := by
  rw [finite_lattice_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation,
    finite_lattice_singleLinkHeatBathDirichletForm_eq_sum_gibbsPairing_fluctuation]
  apply Finset.sum_congr rfl
  intro e _he
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_centered]

/-- A centered Rayleigh contraction certificate for the normalized random-scan
heat-bath operator.  This is the contraction notion exactly dual to the
canonical generator `sum_e Q_e`; no variance-to-Rayleigh conversion is hidden. -/
structure FiniteLatticeWilsonRandomScanRayleighContractionData
    (L : FiniteLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  centered_rayleigh_contraction :
    ∀ f : L.Configuration → ℝ,
      L.gibbsExpectationReal f = 0 →
        L.gibbsPairingReal (L.randomScanHeatBathSweep f) f ≤
          contractionRate * L.gibbsPairingReal f f
  exactGap_le_edgeCard_mul_one_sub_rate :
    exactGapValueReal ≤
      (Fintype.card L.Edge : ℝ) * (1 - contractionRate)

/-- Centered random-scan Rayleigh contraction yields the correctly normalized
finite Wilson heat-bath coercive estimate. -/
theorem finite_lattice_edgeCard_mul_one_sub_randomScanRate_mul_variance_le_dirichlet
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData L)
    (f : L.Configuration → ℝ) :
    ((Fintype.card L.Edge : ℝ) * (1 - R.contractionRate)) *
        L.gibbsVarianceReal f ≤
      L.singleLinkHeatBathDirichletForm f := by
  let centered := L.gibbsCenteredObservable f
  have hCenteredMean : L.gibbsExpectationReal centered = 0 :=
    finite_lattice_gibbsExpectationReal_centered L f
  have hRayleigh := R.centered_rayleigh_contraction centered hCenteredMean
  have hCardNonneg : 0 ≤ (Fintype.card L.Edge : ℝ) := Nat.cast_nonneg _
  calc
    ((Fintype.card L.Edge : ℝ) * (1 - R.contractionRate)) *
        L.gibbsVarianceReal f =
      (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal centered centered -
          R.contractionRate *
            L.gibbsPairingReal centered centered) := by
      rw [finite_lattice_gibbsPairingReal_centered_self]
      ring
    _ ≤ (Fintype.card L.Edge : ℝ) *
        (L.gibbsPairingReal centered centered -
          L.gibbsPairingReal (L.randomScanHeatBathSweep centered) centered) :=
      mul_le_mul_of_nonneg_left
        (sub_le_sub_left hRayleigh
          (L.gibbsPairingReal centered centered))
        hCardNonneg
    _ = L.singleLinkHeatBathDirichletForm centered :=
      (finite_lattice_singleLinkHeatBathDirichletForm_eq_edgeCard_mul_randomScanRayleighDefect
        L R.edgeCard_pos centered).symm
    _ = L.singleLinkHeatBathDirichletForm f :=
      finite_lattice_singleLinkHeatBathDirichletForm_centered L f

/-- A centered random-scan Rayleigh contraction certificate implies the exact
finite Wilson heat-bath Poincare inequality. -/
theorem finite_lattice_exactGap_heatBathPoincare_of_randomScanRayleighContraction
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonRandomScanRayleighContractionData L) :
    L.ExactGapSingleLinkHeatBathPoincare := by
  intro f
  calc
    exactGapValueReal * L.gibbsVarianceReal f ≤
        ((Fintype.card L.Edge : ℝ) *
          (1 - R.contractionRate)) *
            L.gibbsVarianceReal f :=
      mul_le_mul_of_nonneg_right
        R.exactGap_le_edgeCard_mul_one_sub_rate
        (finite_lattice_gibbsVarianceReal_nonneg L f)
    _ ≤ L.singleLinkHeatBathDirichletForm f :=
      finite_lattice_edgeCard_mul_one_sub_randomScanRate_mul_variance_le_dirichlet
        L R f

/-- Uniform centered random-scan Rayleigh contraction data for a finite Wilson
approximation family. -/
structure FiniteLatticeWilsonApproximationFamily.UniformRandomScanRayleighContractionData
    (F : FiniteLatticeWilsonApproximationFamily) where
  edgeCard_pos : ∀ i : F.index, 0 < Fintype.card (F.system i).Edge
  contractionRate : ℝ
  contractionRate_nonneg : 0 ≤ contractionRate
  contractionRate_lt_one : contractionRate < 1
  centered_rayleigh_contraction :
    ∀ (i : F.index) (f : (F.system i).Configuration → ℝ),
      (F.system i).gibbsExpectationReal f = 0 →
        (F.system i).gibbsPairingReal
            ((F.system i).randomScanHeatBathSweep f) f ≤
          contractionRate * (F.system i).gibbsPairingReal f f
  exactGap_le_edgeCard_mul_one_sub_rate :
    ∀ i : F.index,
      exactGapValueReal ≤
        (Fintype.card (F.system i).Edge : ℝ) *
          (1 - contractionRate)

/-- Specialize uniform centered Rayleigh contraction data to one finite Wilson
system. -/
noncomputable def
    FiniteLatticeWilsonApproximationFamily.UniformRandomScanRayleighContractionData.toSystemData
    {F : FiniteLatticeWilsonApproximationFamily}
    (R : F.UniformRandomScanRayleighContractionData)
    (i : F.index) :
    FiniteLatticeWilsonRandomScanRayleighContractionData (F.system i) :=
  { edgeCard_pos := R.edgeCard_pos i
    contractionRate := R.contractionRate
    contractionRate_nonneg := R.contractionRate_nonneg
    contractionRate_lt_one := R.contractionRate_lt_one
    centered_rayleigh_contraction := R.centered_rayleigh_contraction i
    exactGap_le_edgeCard_mul_one_sub_rate :=
      R.exactGap_le_edgeCard_mul_one_sub_rate i }

/-- Uniform centered random-scan Rayleigh contraction implies the family-wide
exact-gap heat-bath Poincare property. -/
theorem finite_lattice_uniform_exactGap_heatBathPoincare_of_randomScanRayleighContraction
    (F : FiniteLatticeWilsonApproximationFamily)
    (R : F.UniformRandomScanRayleighContractionData) :
    F.UniformExactGapSingleLinkHeatBathPoincare := by
  intro i
  exact
    finite_lattice_exactGap_heatBathPoincare_of_randomScanRayleighContraction
      (F.system i) (R.toSystemData i)

end

end MathlibAnalytic
end MGAP4D
