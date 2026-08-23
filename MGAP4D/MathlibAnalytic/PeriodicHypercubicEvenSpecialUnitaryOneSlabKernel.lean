import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSlice
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelRKHSFeature
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProductSpace

noncomputable section

/-- Compact `SU(N)` gauge fields on the canonical time-zero spatial slice of
the modern even-periodic lattice. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
    (H N : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceConfiguration H
    (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Canonical finite ordered list of spatial-slice links. -/
noncomputable def periodicHypercubicEvenSpatialSliceLinkList
    (H : ℕ) : List (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.toList

/-- Canonical finite ordered list of spatial-slice plaquettes. -/
noncomputable def periodicHypercubicEvenSpatialSlicePlaquetteList
    (H : ℕ) : List (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  classical
  exact Finset.univ.toList

@[simp] theorem periodicHypercubicEvenSpatialSliceLink_mem_list
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    e ∈ periodicHypercubicEvenSpatialSliceLinkList H := by
  classical
  simp [periodicHypercubicEvenSpatialSliceLinkList]

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquette_mem_list
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H := by
  classical
  simp [periodicHypercubicEvenSpatialSlicePlaquetteList]

/-- Spatial Wilson action on one canonical time slice. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)).sum

/-- Restricting a full four-dimensional `SU(N)` configuration recovers exactly
the full Wilson plaquette energy on every embedded spatial-slice plaquette. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_restriction_eq
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpatialSliceRestriction A) =
      ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p))).sum := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp_rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restriction_eq]

/-- Half of the spatial Boltzmann amplitude assigned to each end of a symmetric
one-slab transfer kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  Real.exp
    (-(beta / 2) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A)

/-- Spatial half-weights are strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  exact Real.exp_pos _

/-- Temporal-gauge Wilson action of one adjacent Euclidean-time slab.  With the
time-like links gauge-fixed to the identity, each temporal plaquette contributes
the relative boundary holonomy `A(e)⁻¹ B(e)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)).sum

/-- Product of the exact local `SU(N)` Wilson relative kernels over all spatial
links in one adjacent-time slab. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    specialUnitaryWilsonRelativeKernel N beta (A e) (B e)).prod

/-- The finite product of local relative Wilson kernels is exactly the
Boltzmann factor of the temporal-gauge crossing action. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      Real.exp (-beta *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
          H N A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      change
        Real.exp
            (-beta * specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)) *
            Real.exp (-beta *
              (List.map
                (fun e => specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e))
                es).sum) =
          Real.exp (-beta *
            (specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e) +
              (List.map
                (fun e => specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e))
                es).sum))
      rw [← Real.exp_add]
      congr 1
      ring

/-- In particular the actual temporal-gauge crossing kernel is strictly
positive at every pair of spatial boundary configurations. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- Exact RKHS feature realization of the full temporal crossing kernel.  Each
local factor uses the already constructed `SU(N)` Wilson RKHS feature and the
finite product is realized by completed tensor products. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta) := by
  simpa [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel,
    localCrossingWilsonKernel] using
    RealHilbertKernelFeature.listProd
      (periodicHypercubicEvenSpatialSliceLinkList H)
      (fun e A B =>
        localCrossingWilsonKernel N beta (fun X => X e) A B)
      (fun e =>
        localCrossingWilsonKernelConcreteFeature
          N hN beta hbeta (fun X => X e))

/-- The temporal crossing kernel is exactly the inner product of its global
finite-product RKHS features. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
          H N hN beta hbeta).feature A)
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
          H N hN beta hbeta).feature B) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
    H N hN beta hbeta).kernel_eq_inner A B

/-- Symmetric complete one-slab Wilson action: half the spatial action on each
boundary plus all temporal crossing plaquettes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A +
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B +
    (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B

/-- Actual temporal-gauge one-slab Wilson kernel, obtained by sandwiching the
crossing kernel by the two spatial half-Boltzmann amplitudes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H N beta A B *
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta B

/-- Exact Boltzmann formula for the complete compact `SU(N)` one-slab kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B =
      Real.exp (-beta *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  rw [← Real.exp_add, ← Real.exp_add]
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  congr 1
  ring

/-- The complete one-slab kernel is strictly positive pointwise. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- The complete one-slab compact Wilson kernel has an explicit real Hilbert
feature obtained by scaling the crossing feature with the spatial half-weight.
Thus the spatial sandwich preserves Gram positivity without any extra analytic
assumption. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta) := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
      H N hN beta hbeta
  refine
    { FeatureHilbert := C.FeatureHilbert
      feature := fun A =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
          H N beta A • C.feature A
      kernel_eq_inner := ?_ }
  intro A B
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [← C.kernel_eq_inner]
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  ring

/-- Hilbert-feature symmetry of the complete one-slab Wilson kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta B A :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    H N hN beta hbeta).symmetric A B

/-- Positive semidefiniteness of the complete compact `SU(N)` one-slab Wilson
kernel for every finite family of boundary configurations and real
coefficients. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_positiveSemidefinite
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefinite
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    H N hN beta hbeta).positiveSemidefinite

end

end MathlibAnalytic
end MGAP4D
