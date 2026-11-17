import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteBoundaryHaarL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarL2GramSchmidt
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMS — actual time-zero spatial slice, four-edge Haar and gauge modes

The full physical one-slab transfer acts on the Gauss-law fixed subspace of
the *spatial-slice* Haar L², not on the full reflection-fixed boundary Haar L²
used in older primary-plaquette Wilson-energy mode constructions.

This additive stage gives the original time-zero spatial slice its own
literal Fin 4 ↪ spatial-link index, pushes independent normalized SU(N)
Haar coordinates through the actual canonical cyclic plaquette word,
and transports the SU(2) Wilson-energy Gram–Schmidt orthonormal family into
the actual one-slice ambient L². It also proves *pointwise* gauge
invariance of the intrinsic spatial plaquette Wilson-energy powers.

This unit does NOT assert that all of the resulting Haar-L² modes are
already certified members of the physical Gauss-law closed submodule.
That next typed a.e. gauge-pullback step, then a nonzero top-eigenspace
orthogonal mode, is required before proving T_physical != identity.
No abstract OS/physical one-slab identification is made.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMS_sideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMS_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AMS_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AMS_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AMS_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AMS_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AMS_haarLeftInvariant (N : ℕ) :
    MeasureTheory.Measure.IsMulLeftInvariant
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance
local instance p4Q2PZ37AMS_nontrivialSU2 :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Every one of the four *original physical* links of the canonical primary
spatial plaquette has time-zero source and a genuinely spatial direction.
Thus it has a native time-zero spatial-slice link, without selecting an
unrelated boundary representative. -/
noncomputable def p4Q2PZ37AMS_primarySpatialSliceEdge
    (H : ℕ) (k : Fin 4) :
    PeriodicHypercubicEvenSpatialSliceLink H := by
  let e := periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k
  have hv : periodicHypercubicEvenOnPrimaryReflectionPlane H e.1 := by
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane
    fin_cases k <;>
      simp [e, periodicHypercubicEvenPrimarySpatialPlaquetteEdge_zero,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_one,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_two,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_three,
        periodicHypercubicShift_apply]
  have hmu : e.2 ≠ (0 : PeriodicHypercubicAxis) := by
    fin_cases k <;>
      simp [e, periodicHypercubicEvenPrimarySpatialPlaquetteEdge_zero,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_one,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_two,
        periodicHypercubicEvenPrimarySpatialPlaquetteEdge_three]
  exact (⟨e.1, hv⟩, ⟨e.2, hmu⟩)

/-- The native spatial-slice link embeds back to exactly the original
four-dimensional primary plaquette physical edge. -/
@[simp] theorem p4Q2PZ37AMS_primarySpatialSliceEdge_full
    (H : ℕ) (k : Fin 4) :
    periodicHypercubicEvenSpatialSliceLinkEmbedding H
      (p4Q2PZ37AMS_primarySpatialSliceEdge H k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k := by
  rfl

/-- The four canonical original plaquette edges remain pairwise distinct
as *native time-zero spatial-slice* links. -/
noncomputable def p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding
    (H : ℕ) :
    Fin 4 ↪ PeriodicHypercubicEvenSpatialSliceLink H where
  toFun := p4Q2PZ37AMS_primarySpatialSliceEdge H
  inj' := by
    intro i j hij
    apply periodicHypercubicEvenPrimarySpatialPlaquetteEdge_injective H
    have h := congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) hij
    simpa only [p4Q2PZ37AMS_primarySpatialSliceEdge_full] using h

/-- The actual four-edge projection of spatial-slice Haar is exactly the
product of four independent normalized compact SU(N) Haar laws. -/
theorem p4Q2PZ37AMS_measurePreserving_primarySpatialSliceFourEdges
    (H N : ℕ) :
    MeasurePreserving
      (fun (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (k : Fin 4) => A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H k))
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (Measure.pi fun _ : Fin 4 =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  exact measurePreserving_finiteProductProbabilityEmbeddingRestriction μ
    (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H)

/-- Cyclic Wilson plaquette word evaluated on the four actual time-zero
spatial links, without enlarging or replacing the original lattice. -/
noncomputable def p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Matrix.specialUnitaryGroup (Fin N) ℂ :=
  haarFinFourCyclicPlaquetteWord
    (fun k => A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H k))

/-- Under the genuine spatial-slice Haar product, the cyclic four-link
holonomy is exactly normalized compact Haar on SU(N). -/
theorem p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy
    (H N : ℕ) :
    MeasurePreserving
      (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H N)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hEdges :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceFourEdges H N
  have hWord :
      MeasurePreserving
        (haarFinFourCyclicPlaquetteWord :
          (Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) →
            Matrix.specialUnitaryGroup (Fin N) ℂ)
        (Measure.pi fun _ : Fin 4 => μ) μ :=
    measurePreserving_haarFinFourCyclicPlaquetteWord μ
  simpa [μ, p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy,
    Function.comp_def] using hWord.comp hEdges

/-- Actual isometric one-holonomy Haar L² embedding into the *physical
time-zero spatial-slice* ambient Haar L². This is not yet a Gauss-law
submodule isometry. -/
noncomputable def p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback
    (H N : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ)
    (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H N)
    (p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H N)

/-- The explicit SU(2) Wilson-energy Gram–Schmidt sequence is an *actual*
infinite orthonormal family in time-zero spatial-slice Haar L², with no
dimension or density assumption. This is the next-stage input for deriving
a nonzero original Gauss-law top-complement witness. -/
theorem p4Q2PZ37AMS_primarySpatialSliceWilsonEnergy_orthonormal
    (H : ℕ) :
    Orthonormal ℝ
      ((p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2) ∘
        specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode) := by
  exact
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode_orthonormal.comp_linearIsometry
      (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)

/-- The canonical time-zero spatial plaquette with its original axes 1,2. -/
noncomputable def p4Q2PZ37AMS_primarySpatialSlicePlaquette
    (H : ℕ) : PeriodicHypercubicEvenSpatialSlicePlaquette H :=
  (⟨0, by
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
   ⟨((⟨(1 : PeriodicHypercubicAxis), by decide⟩ :
         PeriodicHypercubicEvenSpatialDirection),
      (⟨(2 : PeriodicHypercubicAxis), by decide⟩ :
         PeriodicHypercubicEvenSpatialDirection)), by decide⟩)

/-- Original intrinsic gauge-invariant primary spatial plaquette Wilson-energy
power on the actual time-zero spatial configuration, for every SU(N). -/
noncomputable def p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower
    (H N k : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  specialUnitaryWilsonPlaquetteEnergyPower N k
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))

/-- Pointwise lattice Gauss-law invariance of each original primary spatial
plaquette Wilson-energy power: a genuine conjugacy argument, not an assumed
gauge-invariant representative. -/
theorem p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower_gaugeInvariant
    (H N k : ℕ)
    (γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower H N k
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A) =
      p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower H N k A := by
  unfold p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  exact specialUnitaryWilsonPlaquetteEnergyPower_conjInvariant
    (γ (p4Q2PZ37AMS_primarySpatialSlicePlaquette H).1)
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMS_primarySpatialSliceEdge_full
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMS_measurePreserving_primarySpatialSliceFourEdges
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMS_primarySpatialSliceWilsonEnergy_orthonormal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMS_primarySpatialPlaquetteEnergyPower_gaugeInvariant
