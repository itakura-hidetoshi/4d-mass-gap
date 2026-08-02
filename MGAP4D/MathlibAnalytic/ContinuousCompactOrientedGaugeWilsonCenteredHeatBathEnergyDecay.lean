import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredHeatBathEvolutionL2
import MGAP4D.MathlibAnalytic.RealHilbertBoundedGeneratorEnergyDecay
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

/-- Vacuum centering lands in the orthogonal complement of the normalized
Gibbs vacuum. -/
theorem continuous_compact_oriented_vacuumCenteringL2_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ C.gibbsVacuumL2 (C.vacuumCenteringL2 f) = 0 := by
  rw [continuous_compact_oriented_vacuumCenteringL2_apply]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq,
    continuous_compact_oriented_gibbsVacuumL2_norm]
  ring

/-- The explicit normalized-vacuum centering map is norm nonincreasing. -/
theorem continuous_compact_oriented_vacuumCenteringL2_norm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖C.vacuumCenteringL2 f‖ ≤ ‖f‖ := by
  have hsquare : ‖C.vacuumCenteringL2 f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [continuous_compact_oriented_vacuumCenteringL2_apply]
    unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm,
      norm_smul, continuous_compact_oriented_gibbsVacuumL2_norm]
    simp only [mul_one, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (inner ℝ C.gibbsVacuumL2 f)]
  exact le_of_sq_le_sq hsquare (norm_nonneg _)

/-- Applying the heat-bath Hamiltonian after vacuum centering is the same as
applying it directly. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_vacuumCenteringL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 (C.vacuumCenteringL2 f) =
      C.heatBathHamiltonianL2 f := by
  rw [continuous_compact_oriented_vacuumCenteringL2_apply]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.vacuumCenteredL2
  rw [map_sub, map_smul,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum]
  simp

/-- The heat-bath Hamiltonian has vacuum-orthogonal image. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ C.gibbsVacuumL2 (C.heatBathHamiltonianL2 f) = 0 := by
  rw [← continuous_compact_oriented_heatBathHamiltonianL2_inner_symm
    C C.gibbsVacuumL2 f,
    continuous_compact_oriented_heatBathHamiltonianL2_vacuum,
    inner_zero_left]

/-- Vacuum centering after the heat-bath Hamiltonian is the identity on its
image. -/
theorem continuous_compact_oriented_vacuumCenteringL2_heatBathHamiltonianL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.vacuumCenteringL2 (C.heatBathHamiltonianL2 f) =
      C.heatBathHamiltonianL2 f :=
  continuous_compact_oriented_vacuumCenteringL2_apply_of_orthogonal
    C (C.heatBathHamiltonianL2 f)
    (continuous_compact_oriented_heatBathHamiltonianL2_orthogonal C f)

/-- The heat-bath Hamiltonian commutes with the explicit normalized-vacuum
centering projection. -/
theorem continuous_compact_oriented_heatBathHamiltonianL2_commute_vacuumCenteringL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Commute C.heatBathHamiltonianL2 C.vacuumCenteringL2 := by
  show C.heatBathHamiltonianL2 * C.vacuumCenteringL2 =
    C.vacuumCenteringL2 * C.heatBathHamiltonianL2
  apply ContinuousLinearMap.ext
  intro f
  change C.heatBathHamiltonianL2 (C.vacuumCenteringL2 f) =
    C.vacuumCenteringL2 (C.heatBathHamiltonianL2 f)
  rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuumCenteringL2,
    continuous_compact_oriented_vacuumCenteringL2_heatBathHamiltonianL2]

/-- The actual real-time parameterized half-time heat-bath orbit, started from
the explicitly centered part of a Gibbs `L²` vector. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathOrbitL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (s : ℝ) : Lp ℝ 2 C.gibbsMeasure :=
  NormedSpace.exp
    (s • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2))
    (C.vacuumCenteringL2 f)

@[simp] theorem continuous_compact_oriented_centeredHeatBathOrbitL2_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.centeredHeatBathOrbitL2 f 0 = C.vacuumCenteringL2 f := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathOrbitL2]

/-- The bounded-operator exponential orbit solves the heat-bath generator
ODE with the required half-time normalization. -/
theorem continuous_compact_oriented_centeredHeatBathOrbitL2_hasDerivAt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (s : ℝ) :
    HasDerivAt (C.centeredHeatBathOrbitL2 f)
      ((-(1 / 2 : ℝ)) •
        C.heatBathHamiltonianL2 (C.centeredHeatBathOrbitL2 f s)) s := by
  let B :
      (Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure) :=
    (-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2
  have hop := hasDerivAt_exp_smul_const' B s
  have hconst :
      HasFDerivAt
        (fun _ : ℝ => C.vacuumCenteringL2 f)
        (0 : ℝ →L[ℝ] Lp ℝ 2 C.gibbsMeasure) s :=
    hasFDerivAt_const
      (𝕜 := ℝ) (E := ℝ) (F := Lp ℝ 2 C.gibbsMeasure)
      (C.vacuumCenteringL2 f) s
  have happ := hop.hasFDerivAt.clm_apply hconst
  change HasDerivAt
    (fun y : ℝ =>
      NormedSpace.exp
        (y • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2))
        (C.vacuumCenteringL2 f))
    ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2
      (NormedSpace.exp
        (s • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2))
        (C.vacuumCenteringL2 f))) s
  simpa [B] using happ.hasDerivAt

/-- Every centered heat-bath orbit remains orthogonal to the normalized Gibbs
vacuum. -/
theorem continuous_compact_oriented_centeredHeatBathOrbitL2_orthogonal
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (s : ℝ) :
    inner ℝ C.gibbsVacuumL2 (C.centeredHeatBathOrbitL2 f s) = 0 := by
  have hcommH :=
    continuous_compact_oriented_heatBathHamiltonianL2_commute_vacuumCenteringL2 C
  have hcommExp :
      Commute
        (NormedSpace.exp
          (s • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2)))
        C.vacuumCenteringL2 :=
    (((hcommH.smul_left (-(1 / 2 : ℝ))).smul_left s).exp_left)
  have heq := congrArg
    (fun T : Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure =>
      T (C.vacuumCenteringL2 f)) hcommExp.eq
  change
    NormedSpace.exp
        (s • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2))
        (C.vacuumCenteringL2 (C.vacuumCenteringL2 f)) =
      C.vacuumCenteringL2
        (NormedSpace.exp
          (s • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2))
          (C.vacuumCenteringL2 f)) at heq
  rw [continuous_compact_oriented_vacuumCenteringL2_apply_of_orthogonal
    C (C.vacuumCenteringL2 f)
    (continuous_compact_oriented_vacuumCenteringL2_orthogonal C f)] at heq
  have hfixed :
      C.vacuumCenteringL2 (C.centeredHeatBathOrbitL2 f s) =
        C.centeredHeatBathOrbitL2 f s := by
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathOrbitL2]
      using heq.symm
  have horth := continuous_compact_oriented_vacuumCenteringL2_orthogonal
    C (C.centeredHeatBathOrbitL2 f s)
  rwa [hfixed] at horth

/-- Finite Wilson heat-bath coercivity controls the actual centered exponential
orbit at every real time. -/
theorem continuous_compact_oriented_centeredHeatBathOrbitL2_coercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (s : ℝ) :
    gap * ‖C.centeredHeatBathOrbitL2 f s‖ ^ 2 ≤
      inner ℝ
        (C.heatBathHamiltonianL2 (C.centeredHeatBathOrbitL2 f s))
        (C.centeredHeatBathOrbitL2 f s) :=
  continuous_compact_oriented_centeredHeatBathHamiltonianL2_coercive
    C gap hPoincare (C.centeredHeatBathOrbitL2 f s)
    (continuous_compact_oriented_centeredHeatBathOrbitL2_orthogonal C f s)

/-- The actual centered finite Wilson heat-bath evolution satisfies the sharp
half-time square-root exponential pointwise bound. -/
theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_apply_norm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (t : NNReal)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖C.centeredHeatBathEvolutionL2 t f‖ ≤
      Real.sqrt (Real.exp (-gap * (t : ℝ))) * ‖f‖ := by
  have horbit := realHilbert_boundedGenerator_halfTime_norm_decay
    C.heatBathHamiltonianL2 gap (t : ℝ) t.coe_nonneg
    (C.vacuumCenteringL2 f) (C.centeredHeatBathOrbitL2 f)
    (continuous_compact_oriented_centeredHeatBathOrbitL2_zero C f)
    (continuous_compact_oriented_centeredHeatBathOrbitL2_hasDerivAt C f)
    (continuous_compact_oriented_centeredHeatBathOrbitL2_coercive
      C gap hPoincare f)
  have hcenter := continuous_compact_oriented_vacuumCenteringL2_norm_le C f
  have hfactor : 0 ≤ Real.sqrt (Real.exp (-gap * (t : ℝ))) :=
    Real.sqrt_nonneg _
  have hbound :
      ‖C.centeredHeatBathOrbitL2 f (t : ℝ)‖ ≤
        Real.sqrt (Real.exp (-gap * (t : ℝ))) * ‖f‖ :=
    horbit.trans (mul_le_mul_of_nonneg_left hcenter hfactor)
  have hscale :
      (t : ℝ) • ((-(1 / 2 : ℝ)) • C.heatBathHamiltonianL2) =
        (-((t : ℝ) / 2)) • C.heatBathHamiltonianL2 := by
    rw [smul_smul]
    congr 1
    ring
  have horbit_eq :
      C.centeredHeatBathOrbitL2 f (t : ℝ) =
        C.centeredHeatBathEvolutionL2 t f := by
    simp only [ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathOrbitL2,
      ContinuousCompactOrientedGaugeWilsonSystem.centeredHeatBathEvolutionL2,
      ContinuousCompactOrientedGaugeWilsonSystem.heatBathEvolutionL2,
      ContinuousLinearMap.comp_apply]
    rw [hscale]
  rw [← horbit_eq]
  exact hbound

/-- The centered finite Wilson heat-bath operator norm is generated from the
native Poincaré/coercivity theorem, rather than supplied as independent data. -/
theorem continuous_compact_oriented_centeredHeatBathEvolutionL2_opNorm_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (gap : ℝ)
    (hPoincare : C.HeatBathPoincareL2 gap)
    (t : NNReal) :
    ‖C.centeredHeatBathEvolutionL2 t‖ ≤
      Real.sqrt (Real.exp (-gap * (t : ℝ))) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Real.sqrt_nonneg _
  · intro f
    exact continuous_compact_oriented_centeredHeatBathEvolutionL2_apply_norm_le
      C gap hPoincare t f

end

end MathlibAnalytic
end MGAP4D
