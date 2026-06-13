import MGAP4D.MathlibAnalytic.ContinuousCompactGaugeWilsonIntegrability
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal
open MeasureTheory Set Function

noncomputable section

/-- On a compact group, the normalized left Haar probability measure is also
right invariant.  The proof uses uniqueness of left-invariant finite measures:
right translation of a left Haar measure is again left invariant, and total
mass one forces the scalar of proportionality to be one. -/
theorem normalizedCompactHaar_map_mul_right_eq_self
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (g : G) :
    Measure.map (fun x : G => x * g) (normalizedCompactHaar G) =
      normalizedCompactHaar G := by
  let μ : Measure G := normalizedCompactHaar G
  let μ' : Measure G := Measure.map (fun x : G => x * g) μ
  have hμ'left : IsMulLeftInvariant μ' := by
    dsimp [μ']
    infer_instance
  letI : IsMulLeftInvariant μ' := hμ'left
  have hμ'finite : IsFiniteMeasure μ' := by
    refine ⟨?_⟩
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
    simp [μ]
  letI : IsFiniteMeasure μ' := hμ'finite
  have hμ'compact : IsFiniteMeasureOnCompacts μ' := by infer_instance
  letI : IsFiniteMeasureOnCompacts μ' := hμ'compact
  have hscalar :
      μ' = Measure.haarScalarFactor μ' μ • μ := by
    exact Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
  have huniv := congrArg (fun ν : Measure G => ν Set.univ) hscalar
  have hmapUniv : μ' Set.univ = 1 := by
    dsimp [μ']
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ]
    simp [μ]
  have hscalarOne : Measure.haarScalarFactor μ' μ = 1 := by
    rw [hmapUniv] at huniv
    simpa [μ, ENNReal.smul_def] using huniv.symm
  dsimp [μ'] at hscalar ⊢
  rw [hscalar, hscalarOne, one_smul]

/-- The normalized Haar probability measure on a compact group is bi-invariant. -/
instance normalizedCompactHaar_isMulRightInvariant
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsMulRightInvariant (normalizedCompactHaar G) where
  map_mul_right_eq_self := normalizedCompactHaar_map_mul_right_eq_self G

/-- A fixed left-right affine translation of a compact group preserves normalized
Haar probability measure. -/
theorem normalizedCompactHaar_measurePreserving_mul_left_right
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (a b : G) :
    MeasurePreserving (fun x : G => a * x * b)
      (normalizedCompactHaar G) (normalizedCompactHaar G) := by
  exact
    (measurePreserving_mul_right (normalizedCompactHaar G) b).comp
      (measurePreserving_mul_left (normalizedCompactHaar G) a)

/-- Each link-coordinate affine map induced by a lattice gauge transformation
preserves normalized Haar probability measure. -/
theorem compact_gauge_link_measurePreserving
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation) (e : L.Edge) :
    MeasurePreserving
      (fun x : L.Gauge =>
        γ (L.source e) * x * (γ (L.target e))⁻¹)
      (normalizedCompactHaar L.Gauge)
      (normalizedCompactHaar L.Gauge) :=
  normalizedCompactHaar_measurePreserving_mul_left_right
    L.Gauge (γ (L.source e)) (γ (L.target e))⁻¹

/-- The full lattice gauge transformation preserves the finite product Haar
measure on link configurations. -/
theorem compact_gauge_configurationHaar_measurePreserving
    (L : CompactGaugeWilsonSystem)
    (γ : L.GaugeTransformation) :
    MeasurePreserving (L.gaugeTransform γ)
      L.configurationHaarMeasure L.configurationHaarMeasure := by
  refine ⟨?_, ?_⟩
  · unfold CompactGaugeWilsonSystem.gaugeTransform
    fun_prop
  · unfold CompactGaugeWilsonSystem.configurationHaarMeasure
    rw [Measure.pi_map_pi]
    · congr 1
      funext e
      exact (compact_gauge_link_measurePreserving L γ e).map_eq
    · intro e
      exact (compact_gauge_link_measurePreserving L γ e).measurable.aemeasurable

/-- Exponential tilting preserves a measure-preserving symmetry whenever the
exponent is invariant under that symmetry. -/
theorem measurePreserving_tilted_of_invariant
    {α : Type} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ)
    (hf : Measurable f)
    (hInvariant : ∀ x, f (T x) = f x)
    (hIntegrable : Integrable (fun x => Real.exp (f x)) μ) :
    MeasurePreserving T (μ.tilted f) (μ.tilted f) := by
  refine ⟨hT.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hT.measurable hs]
  rw [MeasureTheory.tilted_apply' μ f (hs.preimage hT.measurable)]
  rw [MeasureTheory.tilted_apply' μ f hs]
  let d : α → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ)
  have hd : Measurable d :=
    ((Real.measurable_exp.comp hf).div_const _).ennreal_ofReal
  have hdInvariant : ∀ x, d (T x) = d x := by
    intro x
    simp only [d, hInvariant x]
  calc
    ∫⁻ x in T ⁻¹' s, d x ∂μ =
        ∫⁻ x in T ⁻¹' s, d (T x) ∂μ := by
          apply setLIntegral_congr_fun (hs.preimage hT.measurable)
          intro x _hx
          exact (hdInvariant x).symm
    _ = ∫⁻ x in s, d x ∂μ :=
      hT.setLIntegral_comp_preimage hs hd

/-- A lattice gauge transformation preserves the continuous compact-gauge
Wilson Gibbs probability measure. -/
theorem continuous_compact_gauge_gibbs_measurePreserving
    (C : ContinuousCompactGaugeWilsonSystem)
    (γ : C.base.GaugeTransformation) :
    MeasurePreserving (C.base.gaugeTransform γ)
      C.gibbsMeasure C.gibbsMeasure := by
  unfold ContinuousCompactGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · exact compact_gauge_configurationHaar_measurePreserving C.base γ
  · exact (continuous_compact_gauge_gibbsExponent C).measurable
  · exact compact_gauge_gibbsExponent_gaugeInvariant C.base γ
  · exact continuous_compact_gauge_boltzmannIntegrable C

/-- Pushforward form of finite-volume Gibbs gauge invariance. -/
theorem continuous_compact_gauge_gibbs_map_eq_self
    (C : ContinuousCompactGaugeWilsonSystem)
    (γ : C.base.GaugeTransformation) :
    Measure.map (C.base.gaugeTransform γ) C.gibbsMeasure = C.gibbsMeasure :=
  (continuous_compact_gauge_gibbs_measurePreserving C γ).map_eq

/-- Gauge invariance of every measurable event under the finite-volume Wilson
Gibbs measure. -/
theorem continuous_compact_gauge_gibbs_preimage_eq
    (C : ContinuousCompactGaugeWilsonSystem)
    (γ : C.base.GaugeTransformation)
    {s : Set C.base.Configuration} (hs : MeasurableSet s) :
    C.gibbsMeasure ((C.base.gaugeTransform γ) ⁻¹' s) =
      C.gibbsMeasure s := by
  have hMP := continuous_compact_gauge_gibbs_measurePreserving C γ
  calc
    C.gibbsMeasure ((C.base.gaugeTransform γ) ⁻¹' s) =
        Measure.map (C.base.gaugeTransform γ) C.gibbsMeasure s := by
          rw [Measure.map_apply hMP.measurable hs]
    _ = C.gibbsMeasure s := by rw [hMP.map_eq]

/-- Family-level statement of actual pushforward gauge invariance. -/
def ContinuousCompactGaugeWilsonApproximationFamily.ActualGaugeInvariant
    (F : ContinuousCompactGaugeWilsonApproximationFamily) : Prop :=
  ∀ (i : F.index) (γ : (F.system i).base.GaugeTransformation),
    Measure.map ((F.system i).base.gaugeTransform γ)
      (F.system i).gibbsMeasure =
    (F.system i).gibbsMeasure

/-- Actual finite-volume gauge invariance is automatic for every continuous
compact-gauge Wilson approximation family. -/
theorem continuous_compact_gauge_family_actualGaugeInvariant
    (F : ContinuousCompactGaugeWilsonApproximationFamily) :
    F.ActualGaugeInvariant := by
  intro i γ
  exact continuous_compact_gauge_gibbs_map_eq_self (F.system i) γ

end

end MathlibAnalytic
end MGAP4D
