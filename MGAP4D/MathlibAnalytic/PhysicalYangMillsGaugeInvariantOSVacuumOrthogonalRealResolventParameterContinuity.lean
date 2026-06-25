import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIdentity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap NNReal

namespace LinearPMap

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The continuous real resolvent, bundled as a family over the open sub-mass
parameter interval. -/
noncomputable def realResolventFamily
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Set.Iio mass → E →L[ℝ] E :=
  fun lambda => A.realResolvent hSelf lambda.property hgap

@[simp] theorem realResolventFamily_apply
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (lambda : Set.Iio mass) :
    A.realResolventFamily hSelf hgap lambda =
      A.realResolvent hSelf lambda.property hgap :=
  rfl

/-- On a parameter region whose distance from the Rayleigh threshold is at
least `delta`, the real resolvent family is uniformly Lipschitz with constant
`delta⁻²` in the operator-norm metric. -/
theorem realResolventFamily_lipschitzOn_subMassTruncation
    (A : E →ₗ.[ℝ] E) {mass delta : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E))
    (hdelta : 0 < delta) :
    LipschitzOnWith (Real.toNNReal (delta⁻¹ * delta⁻¹))
      (A.realResolventFamily hSelf hgap)
      {lambda : Set.Iio mass | (lambda : ℝ) ≤ mass - delta} := by
  apply LipschitzOnWith.of_dist_le'
  intro lambda hlambda mu hmu
  change (lambda : ℝ) ≤ mass - delta at hlambda
  change (mu : ℝ) ≤ mass - delta at hmu
  rw [dist_eq_norm]
  have hdeltaLambda : delta ≤ mass - (lambda : ℝ) := by
    linarith
  have hdeltaMu : delta ≤ mass - (mu : ℝ) := by
    linarith
  have hinvLambda :
      (mass - (lambda : ℝ))⁻¹ ≤ delta⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hdelta hdeltaLambda
  have hinvMu :
      (mass - (mu : ℝ))⁻¹ ≤ delta⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hdelta hdeltaMu
  have hmuInvNonneg : 0 ≤ (mass - (mu : ℝ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr mu.property.le)
  have hdeltaInvNonneg : 0 ≤ delta⁻¹ :=
    inv_nonneg.mpr hdelta.le
  have hproduct :
      (mass - (lambda : ℝ))⁻¹ * (mass - (mu : ℝ))⁻¹ ≤
        delta⁻¹ * delta⁻¹ :=
    mul_le_mul hinvLambda hinvMu hmuInvNonneg hdeltaInvNonneg
  calc
    ‖A.realResolventFamily hSelf hgap lambda -
        A.realResolventFamily hSelf hgap mu‖ ≤
      |(lambda : ℝ) - (mu : ℝ)| *
        ((mass - (lambda : ℝ))⁻¹ * (mass - (mu : ℝ))⁻¹) := by
      simpa only [realResolventFamily_apply] using
        A.realResolvent_sub_norm_le hSelf lambda.property mu.property hgap
    _ ≤ |(lambda : ℝ) - (mu : ℝ)| *
        (delta⁻¹ * delta⁻¹) :=
      mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)
    _ = (delta⁻¹ * delta⁻¹) * dist lambda mu := by
      change |(lambda : ℝ) - (mu : ℝ)| *
          (delta⁻¹ * delta⁻¹) =
        (delta⁻¹ * delta⁻¹) * |(lambda : ℝ) - (mu : ℝ)|
      ring

/-- The sub-mass resolvent family is locally Lipschitz in the operator-norm
metric. -/
theorem realResolventFamily_locallyLipschitz
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    LocallyLipschitz (A.realResolventFamily hSelf hgap) := by
  intro lambda
  let delta : ℝ := (mass - (lambda : ℝ)) / 2
  have hlambdaMass : (lambda : ℝ) < mass := lambda.property
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  refine ⟨Real.toNNReal (delta⁻¹ * delta⁻¹),
    {mu : Set.Iio mass | (mu : ℝ) ≤ mass - delta}, ?_, ?_⟩
  · refine mem_of_superset (Metric.ball_mem_nhds lambda hdelta) ?_
    intro mu hmu
    change (mu : ℝ) ≤ mass - delta
    have hdist : |(mu : ℝ) - (lambda : ℝ)| < delta := by
      simpa [Real.dist_eq] using hmu
    have hlinear : (mu : ℝ) - (lambda : ℝ) < delta :=
      (le_abs_self _).trans_lt hdist
    dsimp [delta] at hlinear ⊢
    linarith
  · exact A.realResolventFamily_lipschitzOn_subMassTruncation
      hSelf hgap hdelta

/-- The real sub-mass resolvent family is continuous in operator norm. -/
theorem realResolventFamily_continuous
    (A : E →ₗ.[ℝ] E) {mass : ℝ}
    (hSelf : IsSelfAdjoint A)
    (hgap : ∀ x : A.domain,
      mass * ‖(x : E)‖ ^ 2 ≤ inner ℝ (A x) (x : E)) :
    Continuous (A.realResolventFamily hSelf hgap) :=
  (A.realResolventFamily_locallyLipschitz hSelf hgap).continuous

end LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The vacuum-orthogonal excitation resolvent bundled over all real parameters
strictly below the transferred mass. -/
noncomputable def FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventFamily
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Set.Iio G.mass →
      P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  fun lambda => G.vacuumOrthogonalRealResolvent T hP hSelf lambda.property

@[simp] theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventFamily_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (lambda : Set.Iio G.mass) :
    G.vacuumOrthogonalRealResolventFamily T hP hSelf lambda =
      G.vacuumOrthogonalRealResolvent T hP hSelf lambda.property :=
  rfl

/-- Uniform operator-norm Lipschitz control on every excitation-resolvent
parameter region separated from the mass threshold by `delta > 0`. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventFamily_lipschitzOn_subMassTruncation
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {delta : ℝ} (hdelta : 0 < delta) :
    LipschitzOnWith (Real.toNNReal (delta⁻¹ * delta⁻¹))
      (G.vacuumOrthogonalRealResolventFamily T hP hSelf)
      {lambda : Set.Iio G.mass | (lambda : ℝ) ≤ G.mass - delta} := by
  apply LipschitzOnWith.of_dist_le'
  intro lambda hlambda mu hmu
  change (lambda : ℝ) ≤ G.mass - delta at hlambda
  change (mu : ℝ) ≤ G.mass - delta at hmu
  rw [dist_eq_norm]
  have hdeltaLambda : delta ≤ G.mass - (lambda : ℝ) := by
    linarith
  have hdeltaMu : delta ≤ G.mass - (mu : ℝ) := by
    linarith
  have hinvLambda :
      (G.mass - (lambda : ℝ))⁻¹ ≤ delta⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hdelta hdeltaLambda
  have hinvMu :
      (G.mass - (mu : ℝ))⁻¹ ≤ delta⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hdelta hdeltaMu
  have hmuInvNonneg : 0 ≤ (G.mass - (mu : ℝ))⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr mu.property.le)
  have hdeltaInvNonneg : 0 ≤ delta⁻¹ :=
    inv_nonneg.mpr hdelta.le
  have hproduct :
      (G.mass - (lambda : ℝ))⁻¹ * (G.mass - (mu : ℝ))⁻¹ ≤
        delta⁻¹ * delta⁻¹ :=
    mul_le_mul hinvLambda hinvMu hmuInvNonneg hdeltaInvNonneg
  calc
    ‖G.vacuumOrthogonalRealResolventFamily T hP hSelf lambda -
        G.vacuumOrthogonalRealResolventFamily T hP hSelf mu‖ ≤
      |(lambda : ℝ) - (mu : ℝ)| *
        ((G.mass - (lambda : ℝ))⁻¹ *
          (G.mass - (mu : ℝ))⁻¹) := by
      simpa only [vacuumOrthogonalRealResolventFamily_apply] using
        G.vacuumOrthogonalRealResolvent_sub_norm_le
          T hP hSelf lambda.property mu.property
    _ ≤ |(lambda : ℝ) - (mu : ℝ)| *
        (delta⁻¹ * delta⁻¹) :=
      mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)
    _ = (delta⁻¹ * delta⁻¹) * dist lambda mu := by
      change |(lambda : ℝ) - (mu : ℝ)| *
          (delta⁻¹ * delta⁻¹) =
        (delta⁻¹ * delta⁻¹) * |(lambda : ℝ) - (mu : ℝ)|
      ring

/-- The excitation resolvent family is locally Lipschitz throughout the real
sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventFamily_locallyLipschitz
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    LocallyLipschitz
      (G.vacuumOrthogonalRealResolventFamily T hP hSelf) := by
  intro lambda
  let delta : ℝ := (G.mass - (lambda : ℝ)) / 2
  have hlambdaMass : (lambda : ℝ) < G.mass := lambda.property
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  refine ⟨Real.toNNReal (delta⁻¹ * delta⁻¹),
    {mu : Set.Iio G.mass | (mu : ℝ) ≤ G.mass - delta}, ?_, ?_⟩
  · refine mem_of_superset (Metric.ball_mem_nhds lambda hdelta) ?_
    intro mu hmu
    change (mu : ℝ) ≤ G.mass - delta
    have hdist : |(mu : ℝ) - (lambda : ℝ)| < delta := by
      simpa [Real.dist_eq] using hmu
    have hlinear : (mu : ℝ) - (lambda : ℝ) < delta :=
      (le_abs_self _).trans_lt hdist
    dsimp [delta] at hlinear ⊢
    linarith
  · exact G.vacuumOrthogonalRealResolventFamily_lipschitzOn_subMassTruncation
      T hP hSelf hdelta

/-- The vacuum-orthogonal excitation resolvent depends continuously on the real
spectral parameter below the transferred mass, in operator norm. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventFamily_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Continuous
      (G.vacuumOrthogonalRealResolventFamily T hP hSelf) :=
  (G.vacuumOrthogonalRealResolventFamily_locallyLipschitz
    T hP hSelf).continuous

/-- Parameter-continuity package for the excitation resolvent below the
transferred mass. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventParameterContinuity_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    Continuous
        (G.vacuumOrthogonalRealResolventFamily T hP hSelf) ∧
      LocallyLipschitz
        (G.vacuumOrthogonalRealResolventFamily T hP hSelf) ∧
      ∀ {delta : ℝ}, 0 < delta →
        LipschitzOnWith (Real.toNNReal (delta⁻¹ * delta⁻¹))
          (G.vacuumOrthogonalRealResolventFamily T hP hSelf)
          {lambda : Set.Iio G.mass |
            (lambda : ℝ) ≤ G.mass - delta} :=
  ⟨G.vacuumOrthogonalRealResolventFamily_continuous T hP hSelf,
    G.vacuumOrthogonalRealResolventFamily_locallyLipschitz T hP hSelf,
    fun hdelta =>
      G.vacuumOrthogonalRealResolventFamily_lipschitzOn_subMassTruncation
        T hP hSelf hdelta⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
