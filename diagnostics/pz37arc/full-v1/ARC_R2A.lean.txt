import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalVacuumCenteredSpectralMomentV5_PZ37ARB
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARC — exact projected double-excitation spectral moment

Project the actual ARB vacuum-centered Haar kernel into the existing
completed physical double-excitation carrier. All excitation matrix
coefficients are preserved. Parseval gives the exact quadratic spectral
sum of the projection, not an assumed identity of the ambient kernel
with the physical carrier. Keep the squared orthogonal leakage explicitly.

The AQY tensor-basis construction is reused at the source level because
its generic helpers are private. The new public statements concern this
orthogonal projection and its spectral moment, not AQY's half-cylinder
residual. No volume-uniform estimate or continuum claim is asserted.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace InnerProduct BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

universe u v w i j

private theorem p4Q2PZ37ARC_basis_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} (b : HilbertBasis ι ℝ E) (L : E →L[ℝ] ℝ)
    (h : ∀ k, L (b k) = 0) (x : E) : L x = 0 := by
  have hs : Submodule.span ℝ (Set.range b) ≤ L.ker := by
    apply Submodule.span_le.2
    rintro _ ⟨k,rfl⟩
    exact h k
  have hc := (Submodule.span ℝ (Set.range b)).topologicalClosure_minimal
    hs L.isClosed_ker
  rw [b.dense_span] at hc
  exact hc (show x ∈ (⊤ : Submodule ℝ E) from Submodule.mem_top)

private theorem p4Q2PZ37ARC_span_orthogonal
    {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : Set V) (z : V) (h : ∀ x ∈ s, inner ℝ z x = 0) :
    z ∈ (Submodule.span ℝ s)ᗮ := by
  have hl : Submodule.span ℝ s ≤ (ℝ ∙ z)ᗮ :=
    Submodule.span_le.2 fun x hx =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.2 (h x hx)
  exact Submodule.orthogonal_le hl
    (Submodule.le_orthogonal_orthogonal (ℝ ∙ z) (Submodule.mem_span_singleton_self z))

/-- A generic complete tensor coefficient sum, proved by constructing the
actual Hilbert basis of the closed span of all bilinear generators. -/
private theorem p4Q2PZ37ARC_tensor_parseval
    {E : Type u} {D : Type v} {V : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : E →ₗ[ℝ] D →ₗ[ℝ] V)
    (hN : ∀ x y, ‖B x y‖ = ‖x‖*‖y‖)
    (hI : ∀ x y f g, inner ℝ (B x y) (B f g) =
      inner ℝ x f * inner ℝ y g)
    (C : Submodule ℝ V)
    (hC : C = (Submodule.span ℝ (Set.range fun p : E × D => B p.1 p.2)).topologicalClosure)
    (z : V) (hz : z ∈ C)
    {ι : Type i} {κ : Type j} (b : HilbertBasis ι ℝ E) (d : HilbertBasis κ ℝ D) :
    HasSum (fun p : ι × κ => (inner ℝ (B (b p.1) (d p.2)) z)^2) (‖z‖^2) := by
  classical
  have hclosed : IsClosed (C : Set V) := by
    rw [hC]
    exact Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace C := hclosed.completeSpace_coe
  let w : ι × κ → C := fun p =>
    ⟨B (b p.1) (d p.2), by
      rw [hC]
      exact (Submodule.span ℝ _).le_topologicalClosure
        (Submodule.subset_span ⟨(b p.1,d p.2),rfl⟩)⟩
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro p q
    change inner ℝ (B (b p.1) (d p.2)) (B (b q.1) (d q.2)) = _
    rw [hI,(orthonormal_iff_ite.mp b.orthonormal) p.1 q.1,
      (orthonormal_iff_ite.mp d.orthonormal) p.2 q.2]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
      simp [h1,h2,Prod.ext_iff]
  have htot : (Submodule.span ℝ (Set.range w))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro r hr
    have htest (a : ι) (c : κ) : inner ℝ (r : V) (B (b a) (d c)) = 0 := by
      have h := (Submodule.mem_orthogonal' _ _).1 hr (w (a,c))
        (Submodule.subset_span ⟨(a,c),rfl⟩)
      exact h
    have hleft (x : E) (c : κ) : inner ℝ (r : V) (B x (d c)) = 0 := by
      let L : E →L[ℝ] V := (B.flip (d c)).mkContinuous ‖d c‖
        (fun y => by change ‖B y (d c)‖ ≤ ‖d c‖*‖y‖; rw [hN,mul_comm])
      exact p4Q2PZ37ARC_basis_zero b ((innerSL ℝ (r : V)).comp L)
        (fun a => htest a c) x
    have hall (x : E) (y : D) : inner ℝ (r : V) (B x y) = 0 := by
      let L : D →L[ℝ] V := (B x).mkContinuous ‖x‖
        (fun q => (hN x q).le)
      exact p4Q2PZ37ARC_basis_zero d ((innerSL ℝ (r : V)).comp L)
        (fun c => hleft x c) y
    have ho0 : (r : V) ∈
        (Submodule.span ℝ (Set.range fun p : E × D => B p.1 p.2)).topologicalClosureᗮ := by
      rw [Submodule.orthogonal_closure]
      apply p4Q2PZ37ARC_span_orthogonal
      rintro _ ⟨⟨x,y⟩,rfl⟩
      exact hall x y
    have ho : (r : V) ∈ Cᗮ :=
      (congrArg (fun P : Submodule ℝ V => (r : V) ∈ Pᗮ) hC).mpr ho0
    exact Subtype.ext (inner_self_eq_zero.mp
      (Submodule.inner_right_of_mem_orthogonal r.property ho))
  let bC : HilbertBasis (ι × κ) ℝ C := HilbertBasis.mkOfOrthogonalEqBot hw htot
  have hbC : ⇑bC = w := HilbertBasis.coe_mkOfOrthogonalEqBot hw htot
  let r : C := ⟨z,hz⟩
  have hs := bC.hasSum_inner_mul_inner r r
  rw [real_inner_self_eq_norm_sq] at hs
  change HasSum _ (‖z‖^2) at hs
  have he : (fun p : ι × κ => inner ℝ r (bC p) * inner ℝ (bC p) r) =
      (fun p : ι × κ => (inner ℝ (B (b p.1) (d p.2)) z)^2) := by
    funext p
    rw [show bC p = w p from congrFun hbC p]
    change inner ℝ z (B (b p.1) (d p.2)) *
      inner ℝ (B (b p.1) (d p.2)) z = _
    rw [show inner ℝ z (B (b p.1) (d p.2)) =
      inner ℝ (B (b p.1) (d p.2)) z from real_inner_comm _ _,pow_two]
  rw [he] at hs
  exact hs

private theorem p4Q2PZ37ARC_matrix_transport
    {E : Type u} {D : Type v} {V : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : E →ₗ[ℝ] D →ₗ[ℝ] V)
    (hN : ∀ x y, ‖B x y‖ = ‖x‖*‖y‖)
    (hI : ∀ x y f g, inner ℝ (B x y) (B f g) =
      inner ℝ x f * inner ℝ y g)
    (C : Submodule ℝ V)
    (hC : C = (Submodule.span ℝ (Set.range fun p : E × D => B p.1 p.2)).topologicalClosure)
    (z : V) (hz : z ∈ C)
    (A : E → D → ℝ) (hA : ∀ f g, inner ℝ (B f g) z = A f g)
    {ι : Type i} {κ : Type j} (b : HilbertBasis ι ℝ E) (d : HilbertBasis κ ℝ D) :
    HasSum (fun p : ι × κ => (A (b p.1) (d p.2))^2) (‖z‖^2) := by
  have hs := p4Q2PZ37ARC_tensor_parseval B hN hI C hC z hz b d
  have he : (fun p : ι × κ => (inner ℝ (B (b p.1) (d p.2)) z)^2) =
      (fun p : ι × κ => (A (b p.1) (d p.2))^2) :=
    funext fun p => congrArg (fun x : ℝ => x^2) (hA (b p.1) (d p.2))
  rw [he] at hs
  exact hs

private def p4Q2PZ37ARC_project_aux {E : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Submodule ℝ E) (hc : IsClosed (C : Set E)) (z : E) : E := by
  letI : CompleteSpace C := hc.completeSpace_coe
  exact C.starProjection z

private theorem p4Q2PZ37ARC_project_mem_aux {E : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Submodule ℝ E) (hc : IsClosed (C : Set E)) (z : E) :
    p4Q2PZ37ARC_project_aux C hc z ∈ C := by
  letI : CompleteSpace C := hc.completeSpace_coe
  change C.starProjection z ∈ C
  exact Submodule.starProjection_apply_mem C z

private theorem p4Q2PZ37ARC_project_inner_aux {E : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Submodule ℝ E) (hc : IsClosed (C : Set E)) (z x : E)
    (hx : x ∈ C) :
    inner ℝ x (p4Q2PZ37ARC_project_aux C hc z) = inner ℝ x z := by
  letI : CompleteSpace C := hc.completeSpace_coe
  change inner ℝ x (C.starProjection z) = inner ℝ x z
  have ho : z - C.starProjection z ∈ Cᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := C) z
  have hh : inner ℝ x (z - C.starProjection z) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hx ho
  rw [inner_sub_right] at hh
  exact (sub_eq_zero.mp hh).symm

private theorem p4Q2PZ37ARC_project_normSq_aux {E : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : Submodule ℝ E) (hc : IsClosed (C : Set E)) (z : E) :
    ‖z‖^2 = ‖p4Q2PZ37ARC_project_aux C hc z‖^2 +
      ‖z-p4Q2PZ37ARC_project_aux C hc z‖^2 := by
  letI : CompleteSpace C := hc.completeSpace_coe
  change ‖z‖^2 = ‖C.starProjection z‖^2 + ‖z-C.starProjection z‖^2
  have hh := C.norm_sq_eq_add_norm_sq_starProjection z
  rw [Submodule.starProjection_orthogonal_val (K := C) z] at hh
  exact hh

private theorem p4Q2PZ37ARC_diagonal_aux
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type i} [DecidableEq ι]
    (t : E →L[ℝ] E) (b : HilbertBasis ι ℝ E) (rho : ι → ℝ)
    (he : ∀ k, t (b k) = rho k • b k) (q : ℝ)
    (hs : HasSum (fun p : ι × ι =>
      (inner ℝ (t (b p.1)) (b p.2))^2) q) :
    HasSum (fun k => (rho k)^2) q := by
  have hfun : (fun p : ι × ι =>
      (inner ℝ (t (b p.1)) (b p.2))^2) =
      (fun p : ι × ι => if p.1 = p.2 then (rho p.1)^2 else 0) := by
    funext p
    rw [he p.1,real_inner_smul_left,(orthonormal_iff_ite.mp b.orthonormal) p.1 p.2]
    by_cases h : p.1 = p.2 <;> simp [h]
  rw [hfun] at hs
  let e : ι → ι × ι := fun k => (k,k)
  let a : ι × ι → ℝ := fun p => if p.1 = p.2 then (rho p.1)^2 else 0
  have heInj : Function.Injective e := fun _ _ h => congrArg Prod.fst h
  have ha0 : ∀ p ∉ Set.range e, a p = 0 := by
    intro p hp
    have hn : p.1 ≠ p.2 := by
      intro hh
      exact hp ⟨p.1,Prod.ext rfl hh⟩
    simp [a,hn]
  have ha : HasSum a q := hs
  have hs' := (heInj.hasSum_iff ha0).2 ha
  simpa [Function.comp_def,e,a] using hs'

private theorem p4Q2PZ37ARC_two_pos : 0 < (2 : ℕ) := by decide

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phys" => PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "Pair" => PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
local notation "Dec" => periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
local notation "K" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
local notation "OO" => periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalBlockClosure
local notation "EH" => periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
local notation "Step" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
local notation "PF" => p4Q2PZ37AQW_partitionFactor
local notation "Res" => p4Q2PZ37AQX_relativeResidual
local notation "Emb" => periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearIsometry

local instance p4Q2PZ37ARC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ARC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ARC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ARC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ARC_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ARC_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance p4Q2PZ37ARC_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37ARC_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ARC_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ARC_nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun g : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private def p4Q2PZ37ARC_bilinear (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    K H 2 (by norm_num) beta hb →ₗ[ℝ]
      (K H 2 (by norm_num) beta hb →ₗ[ℝ] Pair H 2) where
  toFun := fun f => (realL2ExternalTensorLinearMapRight
    (Emb H 2 (by norm_num) beta hb f)).comp (Emb H 2 (by norm_num) beta hb).toLinearMap
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro x
    change realL2ExternalTensor
      (Emb H 2 (by norm_num) beta hb (f+g)) (Emb H 2 (by norm_num) beta hb x) =
        realL2ExternalTensor (Emb H 2 (by norm_num) beta hb f) (Emb H 2 (by norm_num) beta hb x) +
        realL2ExternalTensor (Emb H 2 (by norm_num) beta hb g) (Emb H 2 (by norm_num) beta hb x)
    rw [map_add, realL2ExternalTensor_add_left]
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro x
    change realL2ExternalTensor
      (Emb H 2 (by norm_num) beta hb (c • f)) (Emb H 2 (by norm_num) beta hb x) =
        c • realL2ExternalTensor (Emb H 2 (by norm_num) beta hb f) (Emb H 2 (by norm_num) beta hb x)
    rw [map_smul, realL2ExternalTensor_smul_left]

private theorem p4Q2PZ37ARC_bilinear_norm (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g : K H 2 (by norm_num) beta hb) :
    ‖p4Q2PZ37ARC_bilinear H beta hb f g‖ = ‖f‖*‖g‖ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_norm
    H 2 (by norm_num) beta hb f g

private theorem p4Q2PZ37ARC_bilinear_inner (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g x y : K H 2 (by norm_num) beta hb) :
    inner ℝ (p4Q2PZ37ARC_bilinear H beta hb f g)
      (p4Q2PZ37ARC_bilinear H beta hb x y) =
      inner ℝ f x * inner ℝ g y :=
  realL2ExternalTensor_inner
    (Emb H 2 (by norm_num) beta hb f) (Emb H 2 (by norm_num) beta hb x)
    (Emb H 2 (by norm_num) beta hb g) (Emb H 2 (by norm_num) beta hb y)

private theorem p4Q2PZ37ARC_bilinear_generator (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g : K H 2 (by norm_num) beta hb) :
    p4Q2PZ37ARC_bilinear H beta hb f g =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
        H 2 (by norm_num) beta hb f g := rfl

private theorem p4Q2PZ37ARC_closure_eq (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    OO H 2 (by norm_num) beta hb =
      (Submodule.span ℝ (Set.range fun p :
        K H 2 (by norm_num) beta hb × K H 2 (by norm_num) beta hb =>
          p4Q2PZ37ARC_bilinear H beta hb p.1 p.2)).topologicalClosure := by
  change (Submodule.span ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalGeneratorSet
      H 2 (by norm_num) beta hb)).topologicalClosure = _
  apply congrArg (fun s : Set (Pair H 2) => (Submodule.span ℝ s).topologicalClosure)
  change Set.range (fun p :
    K H 2 (by norm_num) beta hb × K H 2 (by norm_num) beta hb =>
      periodicHypercubicEvenSpecialUnitaryPhysicalPairOrthogonalOrthogonalDecomposableL2
        H 2 (by norm_num) beta hb p.1 p.2) = _
  exact congrArg Set.range (funext fun p =>
    (p4Q2PZ37ARC_bilinear_generator H beta hb p.1 p.2).symm)

local notation "h2" => p4Q2PZ37ARC_two_pos
local notation "CK" => p4Q2PZ37ARB_centeredKernel
local notation "NK" => p4Q2PZ37ARA_normalizedKernel

private theorem p4Q2PZ37ARC_closed (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    IsClosed ((OO H 2 h2 beta hb) : Set (Pair H 2)) :=
  Submodule.isClosed_topologicalClosure _

/-- Orthogonal projection into the actual completed double-excitation block. -/
def p4Q2PZ37ARC_projectedKernel (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  p4Q2PZ37ARC_project_aux (E := Pair H 2)
    (OO H 2 h2 beta hb) (p4Q2PZ37ARC_closed H beta hb) (CK H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_projectedKernel
local notation "PK" => p4Q2PZ37ARC_projectedKernel

/-- Preserve the orthogonal remainder rather than identify ambient and
physical kernels. -/
def p4Q2PZ37ARC_kernelLeakage (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) : Pair H 2 :=
  CK H beta hb - PK H beta hb

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_kernelLeakage
local notation "Leak" => p4Q2PZ37ARC_kernelLeakage

theorem p4Q2PZ37ARC_projected_mem
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    PK H beta hb ∈ OO H 2 h2 beta hb :=
  p4Q2PZ37ARC_project_mem_aux (E := Pair H 2)
    (OO H 2 h2 beta hb) (p4Q2PZ37ARC_closed H beta hb) (CK H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_projected_mem

private theorem p4Q2PZ37ARC_bilinear_mem (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    (f g : K H 2 h2 beta hb) :
    p4Q2PZ37ARC_bilinear H beta hb f g ∈ OO H 2 h2 beta hb := by
  rw [p4Q2PZ37ARC_closure_eq H beta hb]
  exact (Submodule.span ℝ _).le_topologicalClosure
    (Submodule.subset_span ⟨(f,g),rfl⟩)

/-- The physical projection preserves all genuine excitation coefficients. -/
theorem p4Q2PZ37ARC_projected_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : K H 2 h2 beta hb) :
    inner ℝ (realL2ExternalTensor (Emb H 2 h2 beta hb f)
      (Emb H 2 h2 beta hb g)) (PK H beta hb) =
      inner ℝ (Step H 2 h2 beta hb f) g := by
  let x := p4Q2PZ37ARC_bilinear H beta hb f g
  have hx : x ∈ OO H 2 h2 beta hb := p4Q2PZ37ARC_bilinear_mem H beta hb f g
  change inner ℝ x (PK H beta hb) = _
  calc
    _ = inner ℝ x (CK H beta hb) :=
      p4Q2PZ37ARC_project_inner_aux (E := Pair H 2)
        (OO H 2 h2 beta hb) (p4Q2PZ37ARC_closed H beta hb) (CK H beta hb) x hx
    _ = _ := p4Q2PZ37ARB_centered_excitation_inner H beta hb f g

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_projected_inner

private theorem p4Q2PZ37ARC_bilinear_projected_inner
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (f g : K H 2 h2 beta hb) :
    inner ℝ (p4Q2PZ37ARC_bilinear H beta hb f g) (PK H beta hb) =
      inner ℝ (Step H 2 h2 beta hb f) g :=
  p4Q2PZ37ARC_projected_inner H beta hb f g

/-- The complete matrix coefficient budget of the one-step operator. -/
theorem p4Q2PZ37ARC_full_matrix_hasSum
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} {κ : Type j}
    (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (d : HilbertBasis κ ℝ (K H 2 h2 beta hb)) :
    HasSum (fun p : ι × κ =>
      (inner ℝ (Step H 2 h2 beta hb (b p.1)) (d p.2))^2)
      (‖PK H beta hb‖^2) := by
  refine @p4Q2PZ37ARC_matrix_transport
    ↥(K H 2 h2 beta hb)
    ↥(K H 2 h2 beta hb)
    (Pair H 2)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (p4Q2PZ37ARC_bilinear H beta hb) ?_ ?_
    (OO H 2 h2 beta hb) ?_
    (PK H beta hb) ?_
    (fun f g => inner ℝ (Step H 2 h2 beta hb f) g) ?_
    ι κ b d
  · exact p4Q2PZ37ARC_bilinear_norm H beta hb
  · exact p4Q2PZ37ARC_bilinear_inner H beta hb
  · exact p4Q2PZ37ARC_closure_eq H beta hb
  · exact p4Q2PZ37ARC_projected_mem H beta hb
  · exact p4Q2PZ37ARC_bilinear_projected_inner H beta hb

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_full_matrix_hasSum

/-- Exact quadratic spectral sum, retaining the original eigenbasis index
and all multiplicities. -/
theorem p4Q2PZ37ARC_quadratic_hasSum
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    HasSum (fun k => (rho k)^2) (‖PK H beta hb‖^2) := by
  classical
  have hs := @p4Q2PZ37ARC_full_matrix_hasSum H beta hb ι ι b b
  exact @p4Q2PZ37ARC_diagonal_aux
    ↥(K H 2 h2 beta hb) inferInstance inferInstance ι (Classical.decEq ι)
    (Step H 2 h2 beta hb) b rho he (‖PK H beta hb‖^2) hs

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_quadratic_hasSum

theorem p4Q2PZ37ARC_quadratic_tsum
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    (∑' k, (rho k)^2) = ‖PK H beta hb‖^2 :=
  (p4Q2PZ37ARC_quadratic_hasSum H beta hb b rho he).tsum_eq

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_quadratic_tsum

/-- Exact Pythagorean decomposition of the true ambient centered kernel. -/
theorem p4Q2PZ37ARC_normSq_decomposition
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    ‖CK H beta hb‖^2 = ‖PK H beta hb‖^2 + ‖Leak H beta hb‖^2 :=
  p4Q2PZ37ARC_project_normSq_aux (E := Pair H 2)
    (OO H 2 h2 beta hb) (p4Q2PZ37ARC_closed H beta hb) (CK H beta hb)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_normSq_decomposition

/-- Exact defect in ARB's quadratic Bessel bound. The orthogonal remainder
can be nonzero; no independent gauge invariance of the raw kernel is assumed. -/
theorem p4Q2PZ37ARC_quadratic_leakage_identity
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k) :
    ‖NK H beta hb‖^2 - 1 = (∑' k, (rho k)^2) + ‖Leak H beta hb‖^2 := by
  calc
    _ = ‖CK H beta hb‖^2 := (p4Q2PZ37ARB_centered_normSq H beta hb).symm
    _ = ‖PK H beta hb‖^2 + ‖Leak H beta hb‖^2 :=
      p4Q2PZ37ARC_normSq_decomposition H beta hb
    _ = _ := congrArg (fun z : ℝ => z + ‖Leak H beta hb‖^2)
      (p4Q2PZ37ARC_quadratic_tsum H beta hb b rho he).symm

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_quadratic_leakage_identity

private theorem p4Q2PZ37ARC_evenPower_nonneg (r : ℝ) (H : ℕ) :
    0 ≤ r^(2*H) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg r) H

private theorem p4Q2PZ37ARC_scalar_power_bound {ι : Type i}
    (s : Finset ι) (rho : ι → ℝ) (r q : ℝ) (H : ℕ)
    (h0 : ∀ k ∈ s, 0 ≤ rho k) (hr : ∀ k ∈ s, rho k ≤ r)
    (hq : (∑ k ∈ s, (rho k)^2) ≤ q) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤ r^(2*H)*q :=
  (p4Q2PZ37AQZ_finite_power_le_quadratic s rho r H h0 hr).trans
    (mul_le_mul_of_nonneg_left hq (p4Q2PZ37ARC_evenPower_nonneg r H))

/-- Sharpen the finite spectral power budget using only the actual
physical double-excitation projection. -/
theorem p4Q2PZ37ARC_finite_projected_power
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta)
    {ι : Type i} (b : HilbertBasis ι ℝ (K H 2 h2 beta hb))
    (rho : ι → ℝ)
    (he : ∀ k, Step H 2 h2 beta hb (b k) = rho k • b k)
    (s : Finset ι) :
    (∑ k ∈ s, (rho k)^(2*(H+1))) ≤
      ‖Step H 2 h2 beta hb‖^(2*H) * ‖PK H beta hb‖^2 := by
  have hr (k : ι) : 0 ≤ rho k ∧ rho k ≤ ‖Step H 2 h2 beta hb‖ :=
    p4Q2PZ37ARA_eigenvalue_bounds H beta hb (b k)
      (rho k) (b.orthonormal.norm_eq_one k) (he k)
  have hs := p4Q2PZ37ARC_quadratic_hasSum H beta hb b rho he
  have hq : (∑ k ∈ s, (rho k)^2) ≤ ‖PK H beta hb‖^2 :=
    sum_le_hasSum s (fun k _ => sq_nonneg (rho k)) hs
  exact p4Q2PZ37ARC_scalar_power_bound s rho
    ‖Step H 2 h2 beta hb‖ (‖PK H beta hb‖^2) H
    (fun k _ => (hr k).1) (fun k _ => (hr k).2) hq

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_finite_projected_power

theorem p4Q2PZ37ARC_relative_budget_bound
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) :
    (PF H beta hb)⁻¹ ^ 2 - 1 ≤
      ‖Step H 2 h2 beta hb‖^(2*H) * ‖PK H beta hb‖^2 := by
  classical
  obtain ⟨ι,b,rho,he,hs⟩ := p4Q2PZ37AQY_original_spectral_power_hasSum H beta hb
  have hfinite (s : Finset ι) :=
    p4Q2PZ37ARC_finite_projected_power H beta hb b rho he s
  exact hasSum_le_of_sum_le hs hfinite

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_relative_budget_bound

/-- Conditional sufficient criterion in the physical carrier, not the
ambient Haar carrier. The volume-uniform estimate is still open. -/
theorem p4Q2PZ37ARC_partitionFloor_of_projectedBudget
    (beta : ℝ) (hb : 0 ≤ beta)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ H : ℕ, ‖Step H 2 h2 beta hb‖^(2*H) * ‖PK H beta hb‖^2 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : ℕ, c ≤ PF H beta hb := by
  apply (p4Q2PZ37AQX_partitionFloor_iff_relativeResidual_bound beta hb).2
  refine ⟨C,hC,?_⟩
  intro H
  rw [p4Q2PZ37AQX_relativeResidual_normSq H beta hb]
  exact (p4Q2PZ37ARC_relative_budget_bound H beta hb).trans (h H)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARC_partitionFloor_of_projectedBudget

end
end MGAP4D.MathlibAnalytic
