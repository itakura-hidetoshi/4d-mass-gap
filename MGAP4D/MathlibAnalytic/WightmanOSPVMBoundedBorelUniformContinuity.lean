import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMSemigroupOSSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Completed bounded-Borel PVM integration is one-Lipschitz for the uniform
norm.  The estimate is inherited from the finite common-refinement estimate for
simple functions and operator-norm completion. -/
theorem pvmBoundedBorelSpectralIntegralOperator_sub_opNorm_le
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (F G : PVMBoundedBorelRealFunction)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ energy : ℝ, ‖F.toFun energy - G.toFun energy‖ ≤ C) :
    ‖pvmBoundedBorelSpectralIntegralOperator P F -
        pvmBoundedBorelSpectralIntegralOperator P G‖ ≤ C := by
  by_contra hNot
  have hStrict :
      C < ‖pvmBoundedBorelSpectralIntegralOperator P F -
        pvmBoundedBorelSpectralIntegralOperator P G‖ :=
    lt_of_not_ge hNot
  let ε : ℝ :=
    (‖pvmBoundedBorelSpectralIntegralOperator P F -
        pvmBoundedBorelSpectralIntegralOperator P G‖ - C) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hε4 : 0 < ε / 4 := by positivity
  let A := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  let B := explicitBoundedBorelCanonicalSimpleUniformApproximation G
  obtain ⟨NA, hNA⟩ :=
    (Metric.tendsto_atTop.1 (A.tendsto_completedOperator P)) (ε / 4) hε4
  obtain ⟨NB, hNB⟩ :=
    (Metric.tendsto_atTop.1 (B.tendsto_completedOperator P)) (ε / 4) hε4
  obtain ⟨NFA, hNFA⟩ := A.uniform_tendsto (ε / 4) hε4
  obtain ⟨NFB, hNFB⟩ := B.uniform_tendsto (ε / 4) hε4
  let n := max (max NA NB) (max NFA NFB)
  have hnA : NA ≤ n :=
    le_trans (le_max_left NA NB) (le_max_left _ _)
  have hnB : NB ≤ n :=
    le_trans (le_max_right NA NB) (le_max_left _ _)
  have hnFA : NFA ≤ n :=
    le_trans (le_max_left NFA NFB) (le_max_right _ _)
  have hnFB : NFB ≤ n :=
    le_trans (le_max_right NFA NFB) (le_max_right _ _)
  let SA := pvmSimpleFuncSpectralIntegralOperator P (A.simple n)
  let SB := pvmSimpleFuncSpectralIntegralOperator P (B.simple n)
  have hPoint :
      ∀ energy : ℝ, ‖A.simple n energy - B.simple n energy‖ ≤ C + ε / 2 := by
    intro energy
    have hTri :
        ‖A.simple n energy - B.simple n energy‖ ≤
          ‖A.simple n energy - F.toFun energy‖ +
            ‖F.toFun energy - G.toFun energy‖ +
              ‖G.toFun energy - B.simple n energy‖ := by
      calc
        ‖A.simple n energy - B.simple n energy‖ =
            ‖(A.simple n energy - F.toFun energy) +
              (F.toFun energy - G.toFun energy) +
                (G.toFun energy - B.simple n energy)‖ := by
                  congr 1
                  ring
        _ ≤ ‖(A.simple n energy - F.toFun energy) +
              (F.toFun energy - G.toFun energy)‖ +
              ‖G.toFun energy - B.simple n energy‖ := norm_add_le _ _
        _ ≤ (‖A.simple n energy - F.toFun energy‖ +
              ‖F.toFun energy - G.toFun energy‖) +
              ‖G.toFun energy - B.simple n energy‖ := by
                gcongr
                exact norm_add_le _ _
    have hAF := hNFA n hnFA energy
    have hBG : ‖G.toFun energy - B.simple n energy‖ < ε / 4 := by
      simpa [norm_sub_rev] using hNFB n hnFB energy
    have hSumLt :
        ‖A.simple n energy - F.toFun energy‖ +
            ‖F.toFun energy - G.toFun energy‖ +
              ‖G.toFun energy - B.simple n energy‖ <
          C + ε / 2 := by
      nlinarith [hBound energy]
    exact (hTri.trans_lt hSumLt).le
  have hSimple : ‖SA - SB‖ ≤ C + ε / 2 := by
    dsimp [SA, SB]
    exact pvmSimpleFuncSpectralIntegralOperator_sub_opNorm_le
      P (A.simple n) (B.simple n) (C + ε / 2)
        (by positivity) hPoint
  have hAeq :
      A.completedOperator P =
        pvmBoundedBorelSpectralIntegralOperator P F :=
    A.completedOperator_eq_canonical P
  have hBeq :
      B.completedOperator P =
        pvmBoundedBorelSpectralIntegralOperator P G :=
    B.completedOperator_eq_canonical P
  have hLeft :
      ‖pvmBoundedBorelSpectralIntegralOperator P F - SA‖ < ε / 4 := by
    rw [← hAeq]
    simpa [SA, dist_eq_norm, norm_sub_rev] using hNA n hnA
  have hRight :
      ‖SB - pvmBoundedBorelSpectralIntegralOperator P G‖ < ε / 4 := by
    rw [← hBeq]
    simpa [SB, dist_eq_norm] using hNB n hnB
  have hTriangle :
      ‖pvmBoundedBorelSpectralIntegralOperator P F -
          pvmBoundedBorelSpectralIntegralOperator P G‖ ≤
        ‖pvmBoundedBorelSpectralIntegralOperator P F - SA‖ +
          ‖SA - SB‖ +
            ‖SB - pvmBoundedBorelSpectralIntegralOperator P G‖ := by
    calc
      ‖pvmBoundedBorelSpectralIntegralOperator P F -
          pvmBoundedBorelSpectralIntegralOperator P G‖ =
        ‖(pvmBoundedBorelSpectralIntegralOperator P F - SA) +
          (SA - SB) +
            (SB - pvmBoundedBorelSpectralIntegralOperator P G)‖ := by
              congr 1
              module
      _ ≤ ‖(pvmBoundedBorelSpectralIntegralOperator P F - SA) +
              (SA - SB)‖ +
            ‖SB - pvmBoundedBorelSpectralIntegralOperator P G‖ :=
        norm_add_le _ _
      _ ≤ (‖pvmBoundedBorelSpectralIntegralOperator P F - SA‖ +
              ‖SA - SB‖) +
            ‖SB - pvmBoundedBorelSpectralIntegralOperator P G‖ := by
              gcongr
              exact norm_add_le _ _
  have hUpper :
      ‖pvmBoundedBorelSpectralIntegralOperator P F -
          pvmBoundedBorelSpectralIntegralOperator P G‖ < C + ε := by
    exact hTriangle.trans_lt (by linarith)
  dsimp [ε] at hUpper
  linarith

/-- Uniform convergence of bounded-Borel functions along a filter. -/
def PVMBoundedBorelUniformTendsto
    {α : Type*} (l : Filter α)
    (F : α → PVMBoundedBorelRealFunction)
    (G : PVMBoundedBorelRealFunction) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ a in l, ∀ energy : ℝ,
      ‖(F a).toFun energy - G.toFun energy‖ < ε

/-- The completed PVM integral is continuous for uniform convergence of bounded
Borel multipliers. -/
theorem pvmBoundedBorelSpectralIntegralOperator_tendsto_of_uniformTendsto
    {H : Type} {α : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {l : Filter α}
    {F : α → PVMBoundedBorelRealFunction}
    {G : PVMBoundedBorelRealFunction}
    (hUniform : PVMBoundedBorelUniformTendsto l F G) :
    Tendsto
      (fun a => pvmBoundedBorelSpectralIntegralOperator P (F a))
      l (𝓝 (pvmBoundedBorelSpectralIntegralOperator P G)) := by
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [hUniform (ε / 2) hε2] with a ha
  rw [dist_eq_norm]
  exact
    (pvmBoundedBorelSpectralIntegralOperator_sub_opNorm_le
      P (F a) G (ε / 2) hε2.le
        (fun energy => (ha energy).le)).trans_lt
      (half_lt_self hε)

/-- A semigroup spectral multiplier formula together with uniform convergence
of its Hamiltonian difference-quotient multiplier. -/
structure EuclideanYangMillsOSPhysicalSpectralUniformDifferenceQuotient
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  quotientMultiplier :
    ℝ → PVMBoundedBorelRealFunction → PVMBoundedBorelRealFunction
  quotient_uniform_tendsto :
    ∀ (f h : PVMBoundedBorelRealFunction),
      (∀ energy : ℝ, h.toFun energy = energy * f.toFun energy) →
      PVMBoundedBorelUniformTendsto
        (nhdsWithin 0 (Ioi 0))
        (fun t => quotientMultiplier t f) h
  rightDifferenceQuotient_eq_spectralIntegral :
    ∀ (t : ℝ), 0 < t →
      ∀ (f : PVMBoundedBorelRealFunction)
        (ψ : M.toExplicitModel.VacuumOrthogonalHilbert),
      T.rightHamiltonianDifferenceQuotient
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)) t =
        (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              (quotientMultiplier t f) ψ :
            M.toExplicitModel.VacuumOrthogonalHilbert) :
          M.toExplicitModel.H))

/-- Uniform multiplier convergence and the semigroup spectral formula produce
the spectral right-Hamiltonian derivative package required by the coordinate
graph construction. -/
noncomputable def EuclideanYangMillsOSPhysicalSpectralUniformDifferenceQuotient.toSpectralRightHamiltonianValue
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : EuclideanYangMillsOSPhysicalSpectralUniformDifferenceQuotient T) :
    EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T where
  spectralIntegral_hasRightHamiltonianValue := by
    intro f h hCoordinate ψ
    unfold EuclideanYangMillsOSPhysicalTimeTranslation.HasRightHamiltonianValue
    have hUniform := D.quotient_uniform_tendsto f h hCoordinate
    have hSubtype :
        Tendsto
          (fun t =>
            M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              (D.quotientMultiplier t f) ψ)
          (nhdsWithin 0 (Ioi 0))
          (𝓝 (M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
            h ψ)) := by
      refine (Metric.tendsto_nhds).2 ?_
      intro ε hε
      by_cases hψZero : ψ = 0
      · subst ψ
        simp
      · have hψNorm : 0 < ‖ψ‖ := norm_pos_iff.mpr hψZero
        have hεψ : 0 < ε / ‖ψ‖ := div_pos hε hψNorm
        filter_upwards [hUniform (ε / ‖ψ‖) hεψ] with t ht
        rw [dist_eq_norm]
        change
          ‖(M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                (D.quotientMultiplier t f) -
              M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                h) ψ‖ < ε
        have hOperator :
            ‖M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  (D.quotientMultiplier t f) -
                M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  h‖ ≤ ε / ‖ψ‖ :=
          pvmBoundedBorelSpectralIntegralOperator_sub_opNorm_le
            M.toExplicitModel.vacuumOrthogonalSpectralPVM
            (D.quotientMultiplier t f) h (ε / ‖ψ‖) hεψ.le
            (fun energy => (ht energy).le)
        calc
          ‖(M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                (D.quotientMultiplier t f) -
              M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                h) ψ‖ ≤
            ‖M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  (D.quotientMultiplier t f) -
                M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  h‖ * ‖ψ‖ :=
              (M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  (D.quotientMultiplier t f) -
                M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                  h).le_opNorm ψ
          _ ≤ (ε / ‖ψ‖) * ‖ψ‖ :=
            mul_le_mul_of_nonneg_right hOperator (norm_nonneg ψ)
          _ = ε := by field_simp [ne_of_gt hψNorm]
    have hAmbient :
        Tendsto
          (fun t =>
            (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                (D.quotientMultiplier t f) ψ :
              M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)))
          (nhdsWithin 0 (Ioi 0))
          (𝓝 (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H))) := by
      exact (continuous_subtype_val.tendsto _).comp hSubtype
    have hEventually :
        (fun t =>
          T.rightHamiltonianDifferenceQuotient
            (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
              M.toExplicitModel.H)) t) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun t =>
          (((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              (D.quotientMultiplier t f) ψ :
            M.toExplicitModel.VacuumOrthogonalHilbert) :
          M.toExplicitModel.H)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact D.rightDifferenceQuotient_eq_spectralIntegral
        t (by simpa using ht) f ψ
    exact hAmbient.congr' hEventually.symm

end

end MathlibAnalytic
end MGAP4D
