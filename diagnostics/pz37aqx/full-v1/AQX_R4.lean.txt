import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPartitionVacuumOverlapV5_PZ37AQW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairIndependentGaugeFixedEquality
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSNormalizedGramExcitationDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AQX — exact relative excitation kernel of the genuine boundary vacuum

Divide by the positive genuine AQW overlap, not by a surrogate partition.
The relative residual is an actual completed physical pair vector. Its
matrix coefficients are exactly the normalized half-cylinder transfer with
its rank-one top mode removed. All mixed top blocks vanish. The residual
belongs to the completed double-excitation block. A finite orthonormal
spectral budget is necessary; no upper bound for the total budget is assumed.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Pair" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
local notation "J" => periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
local notation "Dec" => periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
local notation "PC" => periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
local notation "Vac" => periodicHypercubicEvenBoundaryVacuumL2
local notation "Omega" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
local notation "Tr" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "NTr" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
local notation "HalfTr" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
local notation "NH" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator
local notation "EH" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
local notation "NormZ" => periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
local notation "Probe" => p4Q2PZ37AQO_endpointProbe
local notation "PF" => p4Q2PZ37AQW_partitionFactor
local notation "TopProbe" => p4Q2PZ37AQW_topProbe
local notation "F" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "TT" => periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
local notation "OT" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan
local notation "TO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan
local notation "OO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockSpan

local instance p4Q2PZ37AQX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AQX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AQX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AQX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AQX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AQX_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37AQX_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37AQX_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37AQX_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37AQX_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem p4Q2PZ37AQX_probe_pair (H : ℕ) (f g : Phys H 2) :
    J H 2 (Probe H f g) = Dec H 2 f g :=
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse H 2
    (Dec H 2 f g)

private theorem p4Q2PZ37AQX_pair_inner (H : ℕ) (f g x y : Phys H 2) :
    inner ℝ (Dec H 2 f g) (Dec H 2 x y) = inner ℝ f x * inner ℝ g y :=
  realL2ExternalTensor_inner (f : Lp ℝ 2 (Mu H 2)) (x : Lp ℝ 2 (Mu H 2))
    (g : Lp ℝ 2 (Mu H 2)) (y : Lp ℝ 2 (Mu H 2))

/-- The original boundary vacuum divided by its own positive AQW overlap,
minus the physical top tensor, on the original ordered two-slice Haar space. -/
def p4Q2PZ37AQX_relativeResidual (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  (PF H beta hb)⁻¹ • J H 2 (Vac H 2 (by norm_num) beta hb) -
    Dec H 2 (Omega H 2 (by norm_num) beta hb) (Omega H 2 (by norm_num) beta hb)

local notation "Res" => p4Q2PZ37AQX_relativeResidual

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual

private theorem p4Q2PZ37AQX_relative_norm_aux {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) (p : ℝ) (hp : p ≠ 0) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℝ x y = p) :
    ‖p⁻¹ • y - x‖^2 = (p⁻¹)^2-1 := by
  rw [norm_sub_sq_real, norm_smul, hy, mul_one, hx, real_inner_smul_left,
    real_inner_comm x y, hxy, Real.norm_eq_abs, sq_abs, inv_mul_cancel₀ hp]
  ring

/-- Exact relative squared norm: the reciprocal squared partition factor
is one plus the genuine excitation kernel's squared L2 norm. -/
theorem p4Q2PZ37AQX_relativeResidual_normSq
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    ‖Res H beta hb‖^2 = (PF H beta hb)⁻¹ ^ 2 - 1 := by
  let o := Omega H 2 (by norm_num) beta hb
  let v := Vac H 2 (by norm_num) beta hb
  let x := Dec H 2 o o
  let y := J H 2 v
  have hmap : J H 2 (TopProbe H beta hb) = x :=
    p4Q2PZ37AQX_probe_pair H o o
  have hx : ‖x‖ = 1 := by
    rw [← hmap, (J H 2).norm_map, p4Q2PZ37AQW_topProbe_norm]
  have hy : ‖y‖ = 1 := by
    exact ((J H 2).norm_map v).trans (p4Q2PZ37APP_originalBoundaryVacuum_norm H beta hb)
  have hxy : inner ℝ x y = PF H beta hb := by
    rw [← hmap]
    exact ((J H 2).inner_map_map (TopProbe H beta hb) v).trans
      (p4Q2PZ37AQW_partitionFactor_eq_overlap H beta hb).symm
  exact p4Q2PZ37AQX_relative_norm_aux x y _ 
    (p4Q2PZ37AQW_partitionFactor_pos_le_one H beta hb).1.ne' hx hy hxy

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_normSq

/-- The residual is in the completed independently gauge-fixed pair carrier,
not merely an ambient boundary vector with some tested coefficients. -/
theorem p4Q2PZ37AQX_relativeResidual_mem_carrier
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    Res H beta hb ∈ PC H 2 := by
  let o := Omega H 2 (by norm_num) beta hb
  have hv := periodicHypercubicEvenBoundaryVacuumPairL2_mem_physicalPairCarrier
    H 2 (by norm_num) beta hb
  have ho : Dec H 2 o o ∈ PC H 2 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H 2).le_topologicalClosure
      (Submodule.subset_span ⟨(o,o),rfl⟩)
  exact (PC H 2).sub_mem ((PC H 2).smul_mem (PF H beta hb)⁻¹ hv) ho

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_mem_carrier

private theorem p4Q2PZ37AQX_inner_scaled_sub {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y z : V) (a : ℝ) :
    inner ℝ x (a • y-z) = a*inner ℝ x y-inner ℝ x z := by
  rw [inner_sub_right,real_inner_smul_right]

private theorem p4Q2PZ37AQX_scalar_cancel (z l : ℝ) (n : ℕ)
    (hz : z ≠ 0) (hl : l ≠ 0) :
    (z*l^n)⁻¹*z = l⁻¹^n := by
  rw [inv_pow]
  field_simp [hz, hl]

private theorem p4Q2PZ37AQX_scaled_inner {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a g : V) (c : ℝ) :
    inner ℝ (c • a) g = c * inner ℝ a g := by
  rw [real_inner_smul_left]

/-- Every physical tensor coefficient of the relative residual is exactly
the normalized genuine half-transfer minus its rank-one top coefficient. -/
theorem p4Q2PZ37AQX_relativeResidual_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : Phys H 2) :
    inner ℝ (Dec H 2 f g) (Res H beta hb) =
      inner ℝ (NH H 2 (by norm_num) beta hb f) g -
        inner ℝ f (Omega H 2 (by norm_num) beta hb) *
        inner ℝ g (Omega H 2 (by norm_num) beta hb) := by
  let p := PF H beta hb
  let z := NormZ H 2 (by norm_num) beta hb
  let l := ‖Tr H 2 (by norm_num) beta hb‖
  let o := Omega H 2 (by norm_num) beta hb
  let y := J H 2 (Vac H 2 (by norm_num) beta hb)
  let a := HalfTr H 2 (by norm_num) beta hb f
  have hp : 0 < p := (p4Q2PZ37AQW_partitionFactor_pos_le_one H beta hb).1
  have hl : 0 < l :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H 2 (by norm_num) beta hb
  have hz : z ≠ 0 := by
    intro hzero
    apply hp.ne'
    change z*l^(H+1) = 0
    rw [hzero,zero_mul]
  have hcancel : p⁻¹*z = l⁻¹^(H+1) :=
    p4Q2PZ37AQX_scalar_cancel z l (H+1) hz hl.ne'
  have hV : inner ℝ (Dec H 2 f g) y = z*inner ℝ a g := by
    calc
      _ = inner ℝ (J H 2 (Probe H f g)) y :=
        congrArg (fun v : Pair H 2 => inner ℝ v y) (p4Q2PZ37AQX_probe_pair H f g).symm
      _ = inner ℝ (Probe H f g) (Vac H 2 (by norm_num) beta hb) :=
        (J H 2).inner_map_map _ _
      _ = _ := p4Q2PZ37AQW_vacuum_probe_inner H beta hb f g
  have hn : NH H 2 (by norm_num) beta hb f = l⁻¹^(H+1) • a :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPositiveHalfCylinderTransferOperator_apply_eq_invNormPow_smul_physical
      H 2 (by norm_num) beta hb f
  have hs : inner ℝ (NH H 2 (by norm_num) beta hb f) g = l⁻¹^(H+1)*inner ℝ a g := by
    calc
      _ = inner ℝ (l⁻¹^(H+1) • a) g :=
        congrArg (fun v : Phys H 2 => inner ℝ v g) hn
      _ = _ := p4Q2PZ37AQX_scaled_inner a g (l⁻¹^(H+1))
  change inner ℝ (Dec H 2 f g) (p⁻¹ • y - Dec H 2 o o) = _
  calc
    _ = p⁻¹*inner ℝ (Dec H 2 f g) y - inner ℝ (Dec H 2 f g) (Dec H 2 o o) :=
      p4Q2PZ37AQX_inner_scaled_sub _ _ _ _
    _ = p⁻¹*(z*inner ℝ a g) - inner ℝ f o*inner ℝ g o := by
      rw [hV,p4Q2PZ37AQX_pair_inner]
    _ = _ := by rw [← mul_assoc,hcancel,← hs]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_inner

private theorem p4Q2PZ37AQX_scaled_fixed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : V →L[ℝ] V) (o : V) (l : ℝ) (hl : l ≠ 0)
    (he : t o = l • o) : (l⁻¹ • t) o = o := by
  change l⁻¹ • t o = o
  rw [he,smul_smul,inv_mul_cancel₀ hl,one_smul]

private theorem p4Q2PZ37AQX_pow_fixed {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : V →L[ℝ] V) (o : V) (he : t o = o) (n : ℕ) : (t^n) o = o := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply,ih,he]

private theorem p4Q2PZ37AQX_pow_inner_fixed {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t : V →L[ℝ] V) (ht : (t : V →ₗ[ℝ] V).IsSymmetric)
    (o f : V) (he : t o = o) (n : ℕ) :
    inner ℝ ((t^n) f) o = inner ℝ f o := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = inner ℝ (t ((t^n) f)) o := by
        rw [pow_succ',ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply]
      _ = inner ℝ ((t^n) f) (t o) := ht _ _
      _ = _ := by rw [he,ih]

private theorem p4Q2PZ37AQX_cancel_left {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t : V →L[ℝ] V) (o g : V) (c : ℝ) (ho : ‖o‖ = 1)
    (he : t o = o) :
    inner ℝ (t (c • o)) g - inner ℝ (c • o) o * inner ℝ g o = 0 := by
  rw [map_smul,he,real_inner_smul_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,ho,real_inner_comm o g]
  ring

private theorem p4Q2PZ37AQX_cancel_right {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (t : V →L[ℝ] V) (o f : V) (c : ℝ) (ho : ‖o‖ = 1)
    (he : inner ℝ (t f) o = inner ℝ f o) :
    inner ℝ (t f) (c • o) - inner ℝ f o * inner ℝ (c • o) o = 0 := by
  rw [real_inner_smul_right,he,real_inner_smul_left,real_inner_self_eq_norm_sq,ho]
  ring

/-- All physical tensor tests with a top endpoint vanish exactly. -/
theorem p4Q2PZ37AQX_relativeResidual_top_endpoint_zero
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : Phys H 2)
    (hfg : f ∈ F H 2 (by norm_num) beta hb ∨ g ∈ F H 2 (by norm_num) beta hb) :
    inner ℝ (Dec H 2 f g) (Res H beta hb) = 0 := by
  let o := Omega H 2 (by norm_num) beta hb
  let t := NTr H 2 (by norm_num) beta hb
  let a := NH H 2 (by norm_num) beta hb
  have ho : ‖o‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hb
  have hnorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
    H 2 (by norm_num) beta hb
  have he : t o = o := p4Q2PZ37AQX_scaled_fixed
    (Tr H 2 (by norm_num) beta hb) o _ hnorm.ne'
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hb)
  have hsym : (t : Phys H 2 →ₗ[ℝ] Phys H 2).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hb
  have hfix : a o = o := p4Q2PZ37AQX_pow_fixed t o he (H+1)
  have hi : inner ℝ (a f) o = inner ℝ f o :=
    p4Q2PZ37AQX_pow_inner_fixed t hsym o f he (H+1)
  have hspan : F H 2 (by norm_num) beta hb = ℝ ∙ o :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector
      H 2 (by norm_num) beta hb
  rw [p4Q2PZ37AQX_relativeResidual_inner]
  change inner ℝ (a f) g - inner ℝ f o * inner ℝ g o = 0
  rcases hfg with hf | hg
  · rw [hspan] at hf
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hf
    rw [← hc]
    exact p4Q2PZ37AQX_cancel_left a o g c ho hfix
  · rw [hspan] at hg
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hg
    rw [← hc]
    exact p4Q2PZ37AQX_cancel_right a o f c ho hi

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_top_endpoint_zero

/-- On two actual excitation vectors the relative kernel coefficient is the
actual restricted half-cylinder transfer matrix coefficient. -/
theorem p4Q2PZ37AQX_relativeResidual_excitation_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g : K H 2 (by norm_num) beta hb) :
    inner ℝ (Dec H 2 (f : Phys H 2) (g : Phys H 2)) (Res H beta hb) =
      inner ℝ (EH H 2 (by norm_num) beta hb f) g := by
  let o := Omega H 2 (by norm_num) beta hb
  have ho : o ∈ F H 2 (by norm_num) beta hb := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector]
    exact Submodule.mem_span_singleton_self _
  have hf := f.property
  change (f : Phys H 2) ∈ (F H 2 (by norm_num) beta hb)ᗮ at hf
  have hz : inner ℝ (f : Phys H 2) o = 0 :=
    Submodule.inner_left_of_mem_orthogonal ho hf
  have hc :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator_coe
      H 2 (by norm_num) beta hb f
  rw [p4Q2PZ37AQX_relativeResidual_inner]
  change inner ℝ (NH H 2 (by norm_num) beta hb (f : Phys H 2)) (g : Phys H 2) -
    inner ℝ (f : Phys H 2) o * inner ℝ (g : Phys H 2) o = _
  rw [hz,zero_mul,sub_zero]
  exact congrArg (fun x : Phys H 2 => inner ℝ x (g : Phys H 2)) hc.symm

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_excitation_inner

private theorem p4Q2PZ37AQX_span_orthogonal {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Set V) (v : V) (h : ∀ x ∈ s, inner ℝ x v = 0) :
    v ∈ (Submodule.span ℝ s)ᗮ := by
  have hle : Submodule.span ℝ s ≤ (ℝ ∙ v)ᗮ :=
    Submodule.span_le.2 fun x hx =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h x hx)
  exact Submodule.orthogonal_le hle
    (Submodule.le_orthogonal_orthogonal (ℝ ∙ v) (Submodule.mem_span_singleton_self v))

private theorem p4Q2PZ37AQX_closed_right {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (A B : Submodule ℝ V) (v : V) (hAB : B ≤ Aᗮ)
    (hV : v ∈ (A ⊔ B).topologicalClosure) (hA : v ∈ Aᗮ) :
    v ∈ B.topologicalClosure := by
  let C := B.topologicalClosure
  have hclosed : IsClosed (C : Set V) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace C := hclosed.completeSpace_coe
  obtain ⟨x,hx,y,hy,he⟩ := C.exists_add_mem_mem_orthogonal v
  have hCA : C ≤ Aᗮ := B.topologicalClosure_minimal hAB A.isClosed_orthogonal
  have hxy : v-x=y := by rw [he]; abel
  have hyA : y ∈ Aᗮ := hxy ▸ (Aᗮ).sub_mem hA (hCA hx)
  have hyB : y ∈ Bᗮ := by
    change y ∈ B.topologicalClosureᗮ at hy
    rwa [Submodule.orthogonal_closure] at hy
  have hyAB : y ∈ (A ⊔ B)ᗮ := by
    rw [← Submodule.inf_orthogonal]
    exact ⟨hyA,hyB⟩
  have hxAB : x ∈ (A ⊔ B).topologicalClosure :=
    Submodule.topologicalClosure_mono (le_sup_right : B ≤ A ⊔ B) hx
  have hyC : y ∈ (A ⊔ B).topologicalClosure := hxy ▸
    ((A ⊔ B).topologicalClosure.sub_mem hV hxAB)
  have hyOrth : y ∈ (A ⊔ B).topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact hyAB
  have hzero : inner ℝ y y = 0 :=
    Submodule.inner_right_of_mem_orthogonal hyC hyOrth
  have hy0 : y = 0 := inner_self_eq_zero.mp hzero
  rw [hy0,add_zero] at he
  rw [he]
  exact hx

/-- Completion step: the genuine relative residual belongs to the double
excitation block, using the existing exact physical-pair carrier theorem. -/
theorem p4Q2PZ37AQX_relativeResidual_mem_doubleExcitation
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    Res H beta hb ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure
      H 2 (by norm_num) beta hb := by
  let tt := TT H 2 (by norm_num) beta hb
  let ot := OT H 2 (by norm_num) beta hb
  let te := TO H 2 (by norm_num) beta hb
  let oo := OO H 2 (by norm_num) beta hb
  let v := Res H beta hb
  have htt : v ∈ ttᗮ := by
    apply p4Q2PZ37AQX_span_orthogonal
    rintro _ ⟨⟨f,g⟩,rfl⟩
    exact p4Q2PZ37AQX_relativeResidual_top_endpoint_zero H beta hb
      (f : Phys H 2) (g : Phys H 2) (Or.inl f.property)
  have hot : v ∈ otᗮ := by
    apply p4Q2PZ37AQX_span_orthogonal
    rintro _ ⟨⟨f,g⟩,rfl⟩
    exact p4Q2PZ37AQX_relativeResidual_top_endpoint_zero H beta hb
      (f : Phys H 2) (g : Phys H 2) (Or.inr g.property)
  have hto : v ∈ teᗮ := by
    apply p4Q2PZ37AQX_span_orthogonal
    rintro _ ⟨⟨f,g⟩,rfl⟩
    exact p4Q2PZ37AQX_relativeResidual_top_endpoint_zero H beta hb
      (f : Phys H 2) (g : Phys H 2) (Or.inl f.property)
  have hA : v ∈ (tt ⊔ (ot ⊔ te))ᗮ := by
    rw [← Submodule.inf_orthogonal,← Submodule.inf_orthogonal]
    exact ⟨htt,hot,hto⟩
  have h1 : tt ⟂ oo :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H 2 (by norm_num) beta hb
  have h2 : ot ⟂ oo :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalTopBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H 2 (by norm_num) beta hb
  have h3 : te ⟂ oo :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairTopOrthogonalBlockSpan_isOrtho_orthogonalOrthogonalBlockSpan
      H 2 (by norm_num) beta hb
  have hO : oo ≤ (tt ⊔ (ot ⊔ te))ᗮ := by
    rw [← Submodule.isOrtho_iff_le,Submodule.isOrtho_sup_right,Submodule.isOrtho_sup_right]
    exact ⟨h1.symm,h2.symm,h3.symm⟩
  have hC : v ∈ ((tt ⊔ (ot ⊔ te)) ⊔ oo).topologicalClosure := by
    have h := p4Q2PZ37AQX_relativeResidual_mem_carrier H beta hb
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_eq_topologicalClosure_topTop_sup_nonTop
      H 2 (by norm_num) beta hb] at h
    change v ∈ (tt ⊔ ((ot ⊔ te) ⊔ oo)).topologicalClosure at h
    rw [sup_assoc]
    exact h
  exact p4Q2PZ37AQX_closed_right _ _ v hO hC hA

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_relativeResidual_mem_doubleExcitation

/-- Every finite rectangle or subset of orthonormal excitation matrix entries
consumes part of the exact relative residual budget (Bessel, not Parseval). -/
theorem p4Q2PZ37AQX_finite_excitation_budget
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι κ : Type*} (s : Finset (ι × κ))
    (f : ι → K H 2 (by norm_num) beta hb)
    (g : κ → K H 2 (by norm_num) beta hb)
    (hf : Orthonormal ℝ f) (hg : Orthonormal ℝ g) :
    (∑ ij ∈ s, (inner ℝ (EH H 2 (by norm_num) beta hb (f ij.1)) (g ij.2))^2)
      ≤ (PF H beta hb)⁻¹ ^ 2 - 1 := by
  classical
  let v : ι × κ → Pair H 2 := fun ij => Dec H 2 (f ij.1 : Phys H 2) (g ij.2 : Phys H 2)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ (Dec H 2 (f i.1 : Phys H 2) (g i.2 : Phys H 2))
      (Dec H 2 (f j.1 : Phys H 2) (g j.2 : Phys H 2)) = _
    rw [p4Q2PZ37AQX_pair_inner]
    change inner ℝ (f i.1) (f j.1) * inner ℝ (g i.2) (g j.2) = _
    rw [(orthonormal_iff_ite.mp hf) i.1 j.1,(orthonormal_iff_ite.mp hg) i.2 j.2]
    by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;>
      simp [h1,h2,Prod.ext_iff]
  have hB := hv.sum_inner_products_le (x := Res H beta hb) (s := s)
  rw [p4Q2PZ37AQX_relativeResidual_normSq] at hB
  simpa only [v,p4Q2PZ37AQX_relativeResidual_excitation_inner,Real.norm_eq_abs,sq_abs] using hB

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_finite_excitation_budget

/-- The target uniform partition floor is exactly a finite bound on the
TOTAL relative excitation budget; finite tests alone do not prove it. -/
theorem p4Q2PZ37AQX_partitionFloor_iff_relativeResidual_bound
    (beta : ℝ) (hb : 0 ≤ beta) :
    (∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, c ≤ PF H beta hb) ↔
      (∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, ‖Res H beta hb‖^2 ≤ C) := by
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨(c⁻¹)^2,sq_nonneg _,?_⟩
    intro H
    rw [p4Q2PZ37AQX_relativeResidual_normSq]
    have hi := inv_anti₀ hc (h H)
    have hs := pow_le_pow_left₀ (inv_nonneg.mpr
      (p4Q2PZ37AQW_partitionFactor_pos_le_one H beta hb).1.le) hi 2
    linarith only [hs]
  · rintro ⟨C,hC,h⟩
    have hc : 0 < C+2 := by linarith
    refine ⟨(C+2)⁻¹,inv_pos.mpr hc,?_⟩
    intro H
    have hp := (p4Q2PZ37AQW_partitionFactor_pos_le_one H beta hb).1
    have hh := h H
    rw [p4Q2PZ37AQX_relativeResidual_normSq] at hh
    have hi : (PF H beta hb)⁻¹ ≤ C+2 := by
      nlinarith only [hh,sq_nonneg ((PF H beta hb)⁻¹-1)]
    have h' := (inv_le_inv₀ hc (inv_pos.mpr hp)).2 hi
    rwa [inv_inv] at h'

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AQX_partitionFloor_iff_relativeResidual_bound

end
end MGAP4D.MathlibAnalytic
