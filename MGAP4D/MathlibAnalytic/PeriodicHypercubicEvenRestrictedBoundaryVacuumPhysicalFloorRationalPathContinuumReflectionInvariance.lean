import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathContinuumFiniteReflectionLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Tactic

/-!
# Full continuum rational-path reflection invariance from finite-dimensional laws

The same-root continuum rational path law is already known to have exactly
reflection-invariant labelled finite-dimensional distributions.  Mathlib's
finite-dimensional-law uniqueness theorem now removes the remaining cylinder
boundary: two process laws on a product measurable space are equal exactly when
all finite restrictions are equal.

We first reindex the merged `Fin m` theorem to an arbitrary finite type.  This
is purely a measurable coordinate equivalence.  We then apply
`ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq` to the two processes

`X_q(x) = x(-q)` and `Y_q(x) = x(q)`.

Every finite restriction is the already proved same-root continuum joint law,
so the complete rational-path probability law is fixed by Euclidean time
reflection:

`map θ μ_cont = μ_cont`, where `θx(q) = x(-q)`.

No OS reflection positivity, Hilbert reconstruction, spectral theorem, decay
estimate, exact mass value, or additional physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory ProbabilityTheory

noncomputable section

local instance continuumPathReflectionInvarianceNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance continuumPathReflectionInvarianceTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuumPathReflectionInvarianceCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuumPathReflectionInvarianceSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuumPathReflectionInvarianceMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuumPathReflectionInvarianceBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The merged labelled `Fin m` continuum reflection theorem is independent of
that particular finite indexing convention: it holds for every finite index
type after measurable reindexing. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_fintype_reflection_jointLaw_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    {ι : Type*} [Fintype ι] (time : ι → ℚ) :
    Measure.map
        (fun x :
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
            H N hN beta hbeta
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.PhysicalConfiguration =>
          fun i : ι => (show ℚ → ℝ from x) (-time i))
        (L.continuumMeasure : Measure _) =
      Measure.map
        (fun x :
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
            H N hN beta hbeta
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
            physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding.PhysicalConfiguration =>
          fun i : ι => (show ℚ → ℝ from x) (time i))
        (L.continuumMeasure : Measure _) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let timeFin : Fin (Fintype.card ι) → ℚ := fun j => time (e.symm j)
  let slotFin : (ℚ → ℝ) → (Fin (Fintype.card ι) → ℝ) :=
    fun x j => x (timeFin j)
  let slotRefFin : (ℚ → ℝ) → (Fin (Fintype.card ι) → ℝ) :=
    fun x j => x (-timeFin j)
  let reindex : (Fin (Fintype.card ι) → ℝ) → (ι → ℝ) :=
    fun y i => y (e i)
  have hslotFin : Measurable slotFin := by
    exact measurable_pi_lambda _ (fun j => measurable_pi_apply (timeFin j))
  have hslotRefFin : Measurable slotRefFin := by
    exact measurable_pi_lambda _ (fun j => measurable_pi_apply (-timeFin j))
  have hreindex : Measurable reindex := by
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))
  have hfin :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_fin_reflection_jointLaw_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L
      (Fintype.card ι) timeFin
  let μ : Measure (ℚ → ℝ) := L.continuumMeasure
  change Measure.map (fun x : ℚ → ℝ => fun i : ι => x (-time i)) μ =
    Measure.map (fun x : ℚ → ℝ => fun i : ι => x (time i)) μ
  calc
    Measure.map (fun x : ℚ → ℝ => fun i : ι => x (-time i)) μ =
        Measure.map (reindex ∘ slotRefFin) μ := by
      congr 1
      funext x i
      simp [reindex, slotRefFin, timeFin, e, Function.comp_def]
    _ = Measure.map reindex (Measure.map slotRefFin μ) :=
      (Measure.map_map hreindex hslotRefFin).symm
    _ = Measure.map reindex (Measure.map slotFin μ) := by
      rw [hfin]
    _ = Measure.map (reindex ∘ slotFin) μ :=
      Measure.map_map hreindex hslotFin
    _ = Measure.map (fun x : ℚ → ℝ => fun i : ι => x (time i)) μ := by
      congr 1
      funext x i
      simp [reindex, slotFin, timeFin, e, Function.comp_def]

/-- Every finite-set restriction of the continuum rational path law is exactly
reflection invariant.  This is the form consumed directly by Mathlib's
finite-dimensional-law uniqueness theorem. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finset_reflection_jointLaw_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding)
    (J : Finset ℚ) :
    Measure.map
        (fun x : ℚ → ℝ => J.restrict
          (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection x))
        (L.continuumMeasure : Measure _) =
      Measure.map
        (fun x : ℚ → ℝ => J.restrict x)
        (L.continuumMeasure : Measure _) := by
  simpa [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection,
    Finset.restrict_def] using
    (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_fintype_reflection_jointLaw_eq_self
      H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L
      (ι := J) (fun q : J => (q : ℚ)))

/-- The complete same-root continuum rational-path probability law is fixed by
Euclidean time reflection.

This is obtained by Mathlib finite-dimensional-law uniqueness from the already
proved continuum finite-cylinder identities; no separate measure-extension
axiom or full-path reflection hypothesis is supplied. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuumMeasure_map_reflection_eq_self
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (physicalVolume : ℕ → ℝ)
    (physicalVolume_tendsto_atTop : Tendsto physicalVolume atTop atTop)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathEmbedding
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero
        physicalVolume physicalVolume_tendsto_atTop).toLatticeEmbedding) :
    Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection
        (L.continuumMeasure : Measure _) =
      (L.continuumMeasure : Measure _) := by
  let μ : Measure (ℚ → ℝ) := L.continuumMeasure
  let X : ℚ → (ℚ → ℝ) → ℝ := fun q x => x (-q)
  let Y : ℚ → (ℚ → ℝ) → ℝ := fun q x => x q
  have hX : AEMeasurable (fun x : ℚ → ℝ => (X · x)) μ := by
    exact
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_measurable.aemeasurable
  have hY : AEMeasurable (fun x : ℚ → ℝ => (Y · x)) μ := by
    exact measurable_id.aemeasurable
  have hLaw :
      Measure.map (fun x : ℚ → ℝ => (X · x)) μ =
        Measure.map (fun x : ℚ → ℝ => (Y · x)) μ := by
    apply
      (ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq hX hY).2
    intro J
    simpa [X, Y,
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection,
      Finset.restrict_def] using
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathFactorial_continuum_finset_reflection_jointLaw_eq_self
        H N hN beta hbeta physicalVolume physicalVolume_tendsto_atTop L J
  change Measure.map
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection μ = μ
  calc
    Measure.map
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection μ =
      Measure.map (fun x : ℚ → ℝ => (X · x)) μ := by
        rfl
    _ = Measure.map (fun x : ℚ → ℝ => (Y · x)) μ := hLaw
    _ = μ := by
      simpa [Y] using (Measure.map_id μ)

end

end MathlibAnalytic
end MGAP4D
