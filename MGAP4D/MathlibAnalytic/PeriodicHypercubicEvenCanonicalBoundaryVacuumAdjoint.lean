import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumL2
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHeatBathVacuumL2
import MGAP4D.MathlibAnalytic.RealHilbertCenteredAdjointFactorization

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance canonicalBoundaryVacuumNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryVacuumTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryVacuumCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryVacuumSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryVacuumMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryVacuumBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Reciprocal-vacuum normalization sends the concrete boundary vacuum moment
to the constant-one vector of the interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2
          H N hN beta hbeta) =
      Lp.const 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta)
        (1 : ℝ) := by
  apply Lp.ext
  have htransport :=
    periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryVacuumL2
        H N hN beta hbeta)
  have hvacuum := periodicHypercubicEven_ae_boundaryHaar_to_marginal
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryVacuumL2_coeFn
      H N hN beta hbeta)
  have hone :
      Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H N hN beta hbeta)
          (1 : ℝ) =ᵐ[
        periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta]
        (fun _ => (1 : ℝ)) :=
    Lp.coeFn_const
  filter_upwards [htransport, hvacuum, hone] with b ht hv ho
  rw [ht, ho]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  rw [hv]
  exact inv_mul_cancel₀
    (ne_of_gt
      (periodicHypercubicEvenBoundaryVacuumMoment_pos
        H N hN beta hbeta b))

/-- Pullback along boundary restriction sends the marginal constant-one vector
to the actual finite Wilson Gibbs vacuum. -/
theorem periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry
        H N hN beta hbeta
        (Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H N hN beta hbeta)
          (1 : ℝ)) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2 := by
  let W := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let hmp :=
    periodicHypercubicEvenSpecialUnitaryBoundaryRestrictionMeasurePreserving
      H N hN beta hbeta
  have htarget : W.gibbsVacuumL2 =
      Lp.const 2 W.gibbsMeasure (1 : ℝ) := by
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsVacuumL2]
  rw [htarget]
  apply Lp.ext
  have hpull :=
    periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry_coeFn
      H N hN beta hbeta
      (Lp.const 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta)
        (1 : ℝ))
  have hmarginal :
      Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H N hN beta hbeta)
          (1 : ℝ) =ᵐ[
        periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta]
        (fun _ => (1 : ℝ)) :=
    Lp.coeFn_const
  have hmarginal_pull := hmp.quasiMeasurePreserving.ae hmarginal
  have hgibbs :
      Lp.const 2 W.gibbsMeasure (1 : ℝ) =ᵐ[W.gibbsMeasure]
        (fun _ => (1 : ℝ)) :=
    Lp.coeFn_const
  filter_upwards [hpull, hmarginal_pull, hgibbs] with A hp hm hg
  rw [hp, hg]
  exact hm

/-- The canonical boundary analysis sends the concrete OS boundary vacuum to
the actual finite Wilson Gibbs vacuum. -/
theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryVacuumL2
          H N hN beta hbeta) =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2 := by
  rw [periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_apply]
  rw [periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry_vacuum]
  exact periodicHypercubicEvenBoundaryMarginalToGibbsL2Isometry_vacuum
    H N hN beta hbeta

/-- Canonical synthesis from finite Wilson Gibbs `L²` back to boundary Haar
`L²` is the Hilbert adjoint of the canonical analysis isometry. -/
noncomputable def periodicHypercubicEvenCanonicalBoundarySynthesisL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure →L[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  realHilbertAdjointSynthesis
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta)

/-- The adjoint synthesis sends the actual finite Gibbs vacuum exactly to the
concrete OS boundary vacuum moment. -/
theorem periodicHypercubicEvenCanonicalBoundarySynthesisL2_vacuum
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2 =
      periodicHypercubicEvenBoundaryVacuumL2
        H N hN beta hbeta := by
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN beta hbeta
  apply ext_inner_right ℝ
  intro f
  unfold periodicHypercubicEvenCanonicalBoundarySynthesisL2
  unfold realHilbertAdjointSynthesis
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [← periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum
    H N hN beta hbeta]
  exact A.inner_map_map
    (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f

/-- The canonical synthesis is a left inverse of canonical analysis. -/
theorem periodicHypercubicEvenCanonicalBoundarySynthesisL2_analysis
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenCanonicalBoundarySynthesisL2
        H N hN beta hbeta
        (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
          H N hN beta hbeta f) = f := by
  let A := periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
    H N hN beta hbeta
  apply ext_inner_right ℝ
  intro g
  unfold periodicHypercubicEvenCanonicalBoundarySynthesisL2
  unfold realHilbertAdjointSynthesis
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact A.inner_map_map f g

/-- Vacuum pairing is transported exactly: a boundary vector is orthogonal to
the OS boundary vacuum iff its canonical Gibbs image is orthogonal to the
finite Gibbs vacuum. -/
theorem periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsVacuumL2
      (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
        H N hN beta hbeta f) =
      inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2
          H N hN beta hbeta) f := by
  rw [← periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry_vacuum
    H N hN beta hbeta]
  exact
    (periodicHypercubicEvenCanonicalBoundaryAnalysisL2Isometry
      H N hN beta hbeta).inner_map_map
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) f

end

end MathlibAnalytic
end MGAP4D
