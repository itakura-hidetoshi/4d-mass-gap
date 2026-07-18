import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCoordinateProjectionProductL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

private theorem continuous_compact_oriented_bcf_abs_le_norm_vacuum_projection
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    |O A| ≤ ‖O‖ := by
  simpa [Real.norm_eq_abs] using O.norm_coe_le_norm A

/-- At zero coupling, Haar averaging in one physical-link coordinate sends a
bounded continuous observable to another bounded continuous observable. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection_continuous_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    Continuous (C.singleLinkHeatBathProjection target O) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ := fun z =>
    O (C.base.replaceLink z.1 target z.2)
  have hF : Continuous F := by
    exact O.continuous.comp
      (continuous_compact_oriented_replaceLink_uncurry C target)
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hMeas : ∀ A : C.base.Configuration,
      AEStronglyMeasurable (fun g : C.base.Gauge => F (A, g))
        (normalizedCompactHaar C.base.Gauge) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound : ∀ A : C.base.Configuration,
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => FB.norm_coe_le_norm (A, g)
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  have hPointwise :
      C.singleLinkHeatBathProjection target O =
        fun A => ∫ g, F (A, g)
          ∂normalizedCompactHaar C.base.Gauge := by
    funext A
    exact
      continuous_compact_oriented_singleLinkHeatBathProjection_eq_haarIntegral_of_beta_eq_zero
        C hBeta target O A
  rw [hPointwise]
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- The zero-coupling one-link Haar average packaged on the bounded-continuous
core. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionBCFOfBetaZero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨C.singleLinkHeatBathProjection target O,
      continuous_compact_oriented_singleLinkHeatBathProjection_continuous_of_beta_eq_zero
        C hBeta target O⟩

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O A =
      C.singleLinkHeatBathProjection target O A :=
  rfl

/-- Ordered finite zero-coupling coordinate sweep on bounded-continuous
observables. The head coordinate acts first. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicCoordinateProjectionListBCFOfBetaZero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0) :
    List C.base.geometry.Edge →
      BoundedContinuousFunction C.base.Configuration ℝ →
      BoundedContinuousFunction C.base.Configuration ℝ
  | [], O => O
  | target :: targets, O =>
      C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O)

@[simp] theorem continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_nil
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.periodicCoordinateProjectionListBCFOfBetaZero hBeta [] O = O :=
  rfl

@[simp] theorem continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_cons
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
        (target :: targets) O =
      C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) :=
  rfl

/-- Pairwise commutation lifted to the bounded-continuous packaging. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_pairwise_comm
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source O) =
      C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) := by
  apply BoundedContinuousFunction.ext
  intro A
  simpa only [continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_apply]
    using congrFun
      (continuous_compact_oriented_singleLinkHeatBathProjection_pairwise_comm_of_beta_eq_zero
        C hBeta target source O) A

/-- Idempotence lifted to the bounded-continuous packaging. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_idempotent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) =
      C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O := by
  apply BoundedContinuousFunction.ext
  intro A
  simpa only [continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_apply]
    using congrFun
      (continuous_compact_oriented_singleLinkHeatBathProjection_idempotent
        C target O) A

/-- A zero-coupling coordinate projection commutes through any finite
bounded-continuous coordinate sweep. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_commute
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target
        (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O) =
      C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) := by
  induction targets generalizing O with
  | nil => rfl
  | cons source rest ih =>
      calc
        C.singleLinkHeatBathProjection target
            (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
              (source :: rest) O) =
          C.singleLinkHeatBathProjection target
            (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source O)) := by
                rfl
        _ = C.periodicCoordinateProjectionListBCFOfBetaZero hBeta rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target
                (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source O)) :=
          ih (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source O)
        _ = C.periodicCoordinateProjectionListBCFOfBetaZero hBeta rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source
                (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O)) := by
          rw [continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_pairwise_comm
            C hBeta target source O]
        _ = C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
              (source :: rest)
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) := by
          rfl

/-- If a coordinate occurs in the finite sweep, its Haar projection fixes the
sweep output pointwise. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_fixed_of_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (hTarget : target ∈ targets)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target
        (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O) =
      C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O := by
  induction targets generalizing O with
  | nil => simp at hTarget
  | cons source rest ih =>
      rcases List.mem_cons.mp hTarget with hEq | hRest
      · subst source
        calc
          C.singleLinkHeatBathProjection target
              (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
                (target :: rest) O) =
            C.periodicCoordinateProjectionListBCFOfBetaZero hBeta rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target
                (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O)) :=
            continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_commute
              C hBeta target rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O)
          _ = C.periodicCoordinateProjectionListBCFOfBetaZero hBeta rest
              (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) := by
            rw [continuous_compact_oriented_singleLinkHeatBathProjectionBCFOfBetaZero_idempotent
              C hBeta target O]
          _ = C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
              (target :: rest) O := by
            rfl
      · exact ih hRest
          (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta source O)

/-- The output of a finite sweep is constant on every coordinate fiber that
occurs in the sweep. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_offLinkFiberConstant_of_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (hTarget : target ∈ targets)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.base.OffLinkFiberConstant target
      (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O) := by
  exact
    (continuous_compact_oriented_singleLinkHeatBathProjection_fixed_iff
      C target
      (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O)).mp
      (continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_fixed_of_mem
        C hBeta target targets hTarget O)

/-- Replace successively the listed coordinates of `A` by their values in `B`. -/
def CompactOrientedGaugeWilsonSystem.replaceLinksFrom
    (L : CompactOrientedGaugeWilsonSystem) :
    List L.geometry.Edge → L.Configuration → L.Configuration → L.Configuration
  | [], A, _B => A
  | target :: targets, A, B =>
      L.replaceLinksFrom targets (L.replaceLink A target (B target)) B

/-- Successive replacement has the expected coordinatewise formula. -/
theorem compact_oriented_replaceLinksFrom_apply
    (L : CompactOrientedGaugeWilsonSystem)
    (targets : List L.geometry.Edge)
    (A B : L.Configuration)
    (edge : L.geometry.Edge) :
    L.replaceLinksFrom targets A B edge =
      if edge ∈ targets then B edge else A edge := by
  classical
  induction targets generalizing A with
  | nil => simp [CompactOrientedGaugeWilsonSystem.replaceLinksFrom]
  | cons target rest ih =>
      rw [CompactOrientedGaugeWilsonSystem.replaceLinksFrom, ih]
      by_cases hRest : edge ∈ rest
      · simp [hRest]
      · by_cases hEq : edge = target
        · subst edge
          simp [hRest]
        · simp [hRest, hEq, CompactOrientedGaugeWilsonSystem.replaceLink]

/-- Replacing every coordinate in the canonical enumeration recovers the
right-hand configuration. -/
theorem continuous_compact_oriented_replaceLinksFrom_periodicPhysicalEdgeEnumeration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration) :
    C.base.replaceLinksFrom C.periodicPhysicalEdgeEnumeration A B = B := by
  classical
  funext edge
  rw [compact_oriented_replaceLinksFrom_apply,
    if_pos (continuous_compact_oriented_periodicPhysicalEdgeEnumeration_mem C edge)]

/-- A function that is constant on every coordinate fiber is unchanged by any
finite sequence of replacements in those coordinates. -/
theorem compact_oriented_replaceLinksFrom_preserves_of_offLinkFiberConstant
    (L : CompactOrientedGaugeWilsonSystem)
    (targets : List L.geometry.Edge)
    (f : L.Configuration → ℝ)
    (hFiber : ∀ target ∈ targets, L.OffLinkFiberConstant target f)
    (A B : L.Configuration) :
    f (L.replaceLinksFrom targets A B) = f A := by
  induction targets generalizing A with
  | nil => rfl
  | cons target rest ih =>
      let A' : L.Configuration := L.replaceLink A target (B target)
      calc
        f (L.replaceLinksFrom (target :: rest) A B) =
            f (L.replaceLinksFrom rest A' B) := by
          rfl
        _ = f A' := ih
          (fun source hSource => hFiber source (List.mem_cons_of_mem target hSource)) A'
        _ = f A := by
          symm
          apply hFiber target List.mem_cons_self A A'
          intro edge hEdge
          simp [A', hEdge]

/-- For a finite coordinate product, invariance under all coordinate fibers
forces pointwise constancy. -/
theorem continuous_compact_oriented_eq_of_forall_offLinkFiberConstant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (hFiber : ∀ target : C.base.geometry.Edge,
      C.base.OffLinkFiberConstant target f)
    (A B : C.base.Configuration) :
    f A = f B := by
  have hPreserves :=
    compact_oriented_replaceLinksFrom_preserves_of_offLinkFiberConstant
      C.base C.periodicPhysicalEdgeEnumeration f
      (fun target _hTarget => hFiber target) A B
  calc
    f A = f (C.base.replaceLinksFrom C.periodicPhysicalEdgeEnumeration A B) :=
      hPreserves.symm
    _ = f B := by
      rw [continuous_compact_oriented_replaceLinksFrom_periodicPhysicalEdgeEnumeration
        C A B]

/-- The complete zero-coupling bounded-continuous coordinate sweep is a
pointwise constant observable. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionBCFOfBetaZero_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
        C.periodicPhysicalEdgeEnumeration O A =
      C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
        C.periodicPhysicalEdgeEnumeration O B := by
  apply continuous_compact_oriented_eq_of_forall_offLinkFiberConstant C
  intro target
  exact
    continuous_compact_oriented_periodicCoordinateProjectionListBCFOfBetaZero_offLinkFiberConstant_of_mem
      C hBeta target C.periodicPhysicalEdgeEnumeration
      (continuous_compact_oriented_periodicPhysicalEdgeEnumeration_mem C target) O

/-- On the bounded-continuous core, one abstract `L²` coordinate projection is
the `L²` class of the packaged concrete beta-zero Haar average. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjectionL2 target (C.gibbsL2RepresentativeBCF O) =
      C.gibbsL2RepresentativeBCF
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O) := by
  let M : ℝ := ‖O‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact norm_nonneg _
  have hOStrong : StronglyMeasurable
      (O : C.base.Configuration → ℝ) :=
    O.continuous.stronglyMeasurable
  have hOBound : ∀ A, |O A| ≤ M := by
    intro A
    dsimp [M]
    exact continuous_compact_oriented_bcf_abs_le_norm_vacuum_projection O A
  have hStep :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_toLp_eq
      C target O hOStrong M hM0 hOBound
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionBCFOfBetaZero]
    using hStep

/-- The abstract ordered `L²` sweep agrees with the packaged concrete sweep on
the bounded-continuous core. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.periodicCoordinateProjectionListL2 targets (C.gibbsL2RepresentativeBCF O) =
      C.gibbsL2RepresentativeBCF
        (C.periodicCoordinateProjectionListBCFOfBetaZero hBeta targets O) := by
  induction targets generalizing O with
  | nil => rfl
  | cons target rest ih =>
      rw [continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_apply,
        continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
          C hBeta target O]
      exact ih
        (C.singleLinkHeatBathProjectionBCFOfBetaZero hBeta target O)

/-- Constant bounded-continuous observable with value `c`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.constantBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ) : BoundedContinuousFunction C.base.Configuration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨(fun _ : C.base.Configuration => c), continuous_const⟩

@[simp] theorem continuous_compact_oriented_constantBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (A : C.base.Configuration) :
    C.constantBCF c A = c :=
  rfl

/-- The Gibbs `L²` representative of a constant bounded-continuous observable
is the corresponding multiple of the normalized Gibbs vacuum. -/
theorem continuous_compact_oriented_gibbsL2RepresentativeBCF_constant
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ) :
    C.gibbsL2RepresentativeBCF (C.constantBCF c) =
      c • C.gibbsVacuumL2 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF
    ContinuousCompactOrientedGaugeWilsonSystem.constantBCF
    ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2
  rw [indicatorConstLp_univ]
  change Lp.const 2 C.gibbsMeasure c = c • Lp.const 2 C.gibbsMeasure (1 : ℝ)
  simpa using
    ((Lp.constₗ 2 C.gibbsMeasure ℝ).map_smul c (1 : ℝ))

/-- Every finite ordered `L²` coordinate sweep preserves the Gibbs-vacuum
coefficient. -/
theorem continuous_compact_oriented_inner_vacuum_periodicCoordinateProjectionListL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ C.gibbsVacuumL2
        (C.periodicCoordinateProjectionListL2 targets f) =
      inner ℝ C.gibbsVacuumL2 f := by
  induction targets generalizing f with
  | nil => rfl
  | cons target rest ih =>
      rw [continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_apply,
        ih]
      calc
        inner ℝ C.gibbsVacuumL2
            (C.singleLinkHeatBathProjectionL2 target f) =
          inner ℝ
            (C.singleLinkHeatBathProjectionL2 target C.gibbsVacuumL2) f := by
              symm
              exact
                continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm
                  C target C.gibbsVacuumL2 f
        _ = inner ℝ C.gibbsVacuumL2 f := by
          rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_vacuum]

/-- On the bounded-continuous Gibbs `L²` core, the full coordinate sweep is
exactly the Gibbs-vacuum rank-one projection. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_gibbsL2RepresentativeBCF_eq_vacuumProjection_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.periodicFullCoordinateProjectionL2 (C.gibbsL2RepresentativeBCF O) =
      inner ℝ C.gibbsVacuumL2 (C.gibbsL2RepresentativeBCF O) •
        C.gibbsVacuumL2 := by
  let QO : BoundedContinuousFunction C.base.Configuration ℝ :=
    C.periodicCoordinateProjectionListBCFOfBetaZero hBeta
      C.periodicPhysicalEdgeEnumeration O
  let A0 : C.base.Configuration := fun _ => 1
  let c : ℝ := QO A0
  have hQOConstant : QO = C.constantBCF c := by
    ext A
    exact
      continuous_compact_oriented_periodicFullCoordinateProjectionBCFOfBetaZero_constant
        C hBeta O A A0
  have hCore :
      C.periodicFullCoordinateProjectionL2 (C.gibbsL2RepresentativeBCF O) =
        C.gibbsL2RepresentativeBCF QO := by
    exact
      continuous_compact_oriented_periodicCoordinateProjectionListL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        C hBeta C.periodicPhysicalEdgeEnumeration O
  have hCoefficient :=
    continuous_compact_oriented_inner_vacuum_periodicCoordinateProjectionListL2
      C C.periodicPhysicalEdgeEnumeration (C.gibbsL2RepresentativeBCF O)
  change
    inner ℝ C.gibbsVacuumL2
        (C.periodicFullCoordinateProjectionL2 (C.gibbsL2RepresentativeBCF O)) =
      inner ℝ C.gibbsVacuumL2 (C.gibbsL2RepresentativeBCF O) at hCoefficient
  have hc : c = inner ℝ C.gibbsVacuumL2 (C.gibbsL2RepresentativeBCF O) := by
    rw [hCore, hQOConstant,
      continuous_compact_oriented_gibbsL2RepresentativeBCF_constant] at hCoefficient
    simpa [real_inner_smul_right, real_inner_self_eq_norm_sq,
      continuous_compact_oriented_gibbsVacuumL2_norm] using hCoefficient
  rw [hCore, hQOConstant,
    continuous_compact_oriented_gibbsL2RepresentativeBCF_constant, hc]

/-- At zero coupling, the full finite coordinate product is the orthogonal
rank-one projection onto the normalized Gibbs-vacuum line on the whole Gibbs
`L²` space. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_eq_vacuumProjection_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicFullCoordinateProjectionL2 f =
      inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
  let p : Lp ℝ 2 C.gibbsMeasure → Prop := fun q =>
    C.periodicFullCoordinateProjectionL2 q =
      inner ℝ C.gibbsVacuumL2 q • C.gibbsVacuumL2
  apply DenseRange.induction_on (p := p)
    (BoundedContinuousFunction.toLp_denseRange
      ℝ C.gibbsMeasure ℝ (by norm_num)) f
  · apply isClosed_eq
    · exact C.periodicFullCoordinateProjectionL2.continuous
    · exact
        (continuous_const.inner continuous_id).smul continuous_const
  · intro O
    change p (BoundedContinuousFunction.toLp 2 C.gibbsMeasure ℝ O)
    simpa [p,
      ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF] using
      continuous_compact_oriented_periodicFullCoordinateProjectionL2_gibbsL2RepresentativeBCF_eq_vacuumProjection_of_beta_eq_zero
        C hBeta O

/-- At zero coupling, the native heat-bath Hamiltonian kernel is exactly the
normalized Gibbs-vacuum line. -/
theorem continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_eq_inner_smul_vacuum_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2 := by
  rw [continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_fullCoordinateProjection_fixed_of_beta_eq_zero
      C hBeta f,
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_eq_vacuumProjection_of_beta_eq_zero
      C hBeta f]
  exact eq_comm

/-- The actual side-three periodic `SU(2)` beta-zero full coordinate product is
exactly the Gibbs-vacuum rank-one projection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_eq_vacuumProjection
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_eq_vacuumProjection_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- For the actual side-three periodic `SU(2)` endpoint system, the native
heat-bath Hamiltonian kernel is precisely the Gibbs-vacuum line. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 := by
  exact
    continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_eq_inner_smul_vacuum_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- Compact receipt for the actual beta-zero vacuum-line identification. This
is finite-volume and does not assert variance tensorization, a Poincare bound,
a random-scan rate, a positive variational lower edge, volume uniformity, a
continuum limit, or a Yang--Mills mass gap. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullCoordinateVacuumProjectionL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f =
      inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      f = inner ℝ
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2)

/-- The actual beta-zero full-coordinate vacuum-projection receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullCoordinateVacuumProjectionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFullCoordinateVacuumProjectionL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_eq_vacuumProjection,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_eq_inner_smul_vacuum⟩

end

end MathlibAnalytic
end MGAP4D
