import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelUniformContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Restriction of a bounded Borel multiplier to a measurable energy set. -/
def pvmBoundedBorelRestrict
    (s : Set ℝ) (hs : MeasurableSet s)
    (f : PVMBoundedBorelRealFunction) : PVMBoundedBorelRealFunction where
  toFun := fun energy => if energy ∈ s then f.toFun energy else 0
  measurable_toFun :=
    Measurable.ite hs f.measurable_toFun measurable_const
  bounded_toFun := by
    obtain ⟨C, hC⟩ := f.bounded_toFun
    have hCnonneg : 0 ≤ C :=
      le_trans (norm_nonneg (f.toFun 0)) (hC 0)
    refine ⟨C, ?_⟩
    intro energy
    by_cases henergy : energy ∈ s
    · simpa [pvmBoundedBorelRestrict, henergy] using hC energy
    · simp [pvmBoundedBorelRestrict, henergy, hCnonneg]

@[simp] theorem pvmBoundedBorelRestrict_apply
    (s : Set ℝ) (hs : MeasurableSet s)
    (f : PVMBoundedBorelRealFunction) (energy : ℝ) :
    (pvmBoundedBorelRestrict s hs f).toFun energy =
      if energy ∈ s then f.toFun energy else 0 :=
  rfl

/-- Symmetric compact energy window used for the compact/tail decomposition. -/
def pvmEnergyWindow (R : ℝ) : Set ℝ := Set.Icc (-R) R

/-- Every symmetric compact energy window is Borel measurable. -/
theorem measurableSet_pvmEnergyWindow (R : ℝ) :
    MeasurableSet (pvmEnergyWindow R) := by
  exact measurableSet_Icc

/-- Subtracting the restriction to a measurable set leaves exactly the
restriction to its complement. -/
theorem pvmBoundedBorelSub_restrict_eq_restrict_compl
    (f : PVMBoundedBorelRealFunction)
    (s : Set ℝ) (hs : MeasurableSet s) :
    pvmBoundedBorelSub f (pvmBoundedBorelRestrict s hs f) =
      pvmBoundedBorelRestrict sᶜ hs.compl f := by
  apply PVMBoundedBorelRealFunction.ext
  funext energy
  by_cases henergy : energy ∈ s <;>
    simp [pvmBoundedBorelSub, pvmBoundedBorelRestrict, henergy]

/-- Operator form of the measurable compact/tail decomposition. -/
theorem pvmBoundedBorelSpectralIntegralOperator_sub_restrict
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : PVMBoundedBorelRealFunction)
    (s : Set ℝ) (hs : MeasurableSet s) :
    pvmBoundedBorelSpectralIntegralOperator P f -
        pvmBoundedBorelSpectralIntegralOperator P
          (pvmBoundedBorelRestrict s hs f) =
      pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelRestrict sᶜ hs.compl f) := by
  rw [← pvmBoundedBorelSpectralIntegralOperator_sub]
  rw [pvmBoundedBorelSub_restrict_eq_restrict_compl]

/-- Vector form of the measurable compact/tail decomposition. -/
theorem pvmBoundedBorelSpectralIntegralOperator_sub_restrict_apply
    {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (f : PVMBoundedBorelRealFunction)
    (s : Set ℝ) (hs : MeasurableSet s) (ψ : H) :
    pvmBoundedBorelSpectralIntegralOperator P f ψ -
        pvmBoundedBorelSpectralIntegralOperator P
          (pvmBoundedBorelRestrict s hs f) ψ =
      pvmBoundedBorelSpectralIntegralOperator P
        (pvmBoundedBorelRestrict sᶜ hs.compl f) ψ := by
  simpa using congrArg
    (fun T : H →L[ℝ] H => T ψ)
    (pvmBoundedBorelSpectralIntegralOperator_sub_restrict P f s hs)

/-- Compact-uniform convergence plus small spectral tails at one vector.

This is the strong-convergence replacement for global uniform multiplier
convergence.  The compact part is controlled pointwise on one finite energy
window, while both the approximating and target spectral tails are small after
PVM integration at the selected vector. -/
def PVMBoundedBorelCompactTailTendstoAtVector
    {H α : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (l : Filter α)
    (F : α → PVMBoundedBorelRealFunction)
    (G : PVMBoundedBorelRealFunction)
    (ψ : H) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ᶠ a in l,
        ‖pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict
              (pvmEnergyWindow R)ᶜ
              (measurableSet_pvmEnergyWindow R).compl
              (F a)) ψ‖ < ε / 4) ∧
      ‖pvmBoundedBorelSpectralIntegralOperator P
          (pvmBoundedBorelRestrict
            (pvmEnergyWindow R)ᶜ
            (measurableSet_pvmEnergyWindow R).compl
            G) ψ‖ < ε / 4 ∧
      (∀ᶠ a in l, ∀ energy : ℝ,
        energy ∈ pvmEnergyWindow R →
          ‖(F a).toFun energy - G.toFun energy‖ <
            ε / (8 * (‖ψ‖ + 1)))

/-- Compact-uniform multiplier convergence and small integrated spectral tails
imply strong convergence of the completed PVM integrals at the selected vector. -/
theorem pvmBoundedBorelSpectralIntegralOperator_tendsto_atVector_of_compactTail
    {H α : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {l : Filter α}
    {F : α → PVMBoundedBorelRealFunction}
    {G : PVMBoundedBorelRealFunction}
    (ψ : H)
    (hCompactTail :
      PVMBoundedBorelCompactTailTendstoAtVector P l F G ψ) :
    Tendsto
      (fun a => pvmBoundedBorelSpectralIntegralOperator P (F a) ψ)
      l
      (𝓝 (pvmBoundedBorelSpectralIntegralOperator P G ψ)) := by
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  rcases hCompactTail ε hε with
    ⟨R, hR, hTailF, hTailG, hCompact⟩
  let K : Set ℝ := pvmEnergyWindow R
  have hK : MeasurableSet K := measurableSet_pvmEnergyWindow R
  let δ : ℝ := ε / (8 * (‖ψ‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [hTailF, hCompact] with a haTail haCompact
  rw [dist_eq_norm]
  have hFirst :
      ‖pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
          pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK (F a)) ψ‖ < ε / 4 := by
    rw [pvmBoundedBorelSpectralIntegralOperator_sub_restrict_apply
      P (F a) K hK ψ]
    simpa [K] using haTail
  have hThird :
      ‖pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK G) ψ -
          pvmBoundedBorelSpectralIntegralOperator P G ψ‖ < ε / 4 := by
    rw [norm_sub_rev,
      pvmBoundedBorelSpectralIntegralOperator_sub_restrict_apply
        P G K hK ψ]
    simpa [K] using hTailG
  have hPoint :
      ∀ energy : ℝ,
        ‖(pvmBoundedBorelRestrict K hK (F a)).toFun energy -
            (pvmBoundedBorelRestrict K hK G).toFun energy‖ ≤ δ := by
    intro energy
    by_cases henergy : energy ∈ K
    · have hLocal := haCompact energy (by simpa [K] using henergy)
      simpa [pvmBoundedBorelRestrict, henergy, δ] using hLocal.le
    · simp [pvmBoundedBorelRestrict, henergy, hδ.le]
  have hOperator :
      ‖pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK (F a)) -
          pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK G)‖ ≤ δ :=
    pvmBoundedBorelSpectralIntegralOperator_sub_opNorm_le
      P
      (pvmBoundedBorelRestrict K hK (F a))
      (pvmBoundedBorelRestrict K hK G)
      δ hδ.le hPoint
  have hCentral :
      ‖pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK (F a)) ψ -
          pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK G) ψ‖ < ε / 4 := by
    change
      ‖(pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK (F a)) -
          pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK G)) ψ‖ < ε / 4
    have hψLe : ‖ψ‖ ≤ ‖ψ‖ + 1 := by linarith
    calc
      ‖(pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK (F a)) -
          pvmBoundedBorelSpectralIntegralOperator P
            (pvmBoundedBorelRestrict K hK G)) ψ‖ ≤
        ‖pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK (F a)) -
            pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK G)‖ * ‖ψ‖ :=
          (pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK (F a)) -
            pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK G)).le_opNorm ψ
      _ ≤ δ * ‖ψ‖ :=
        mul_le_mul_of_nonneg_right hOperator (norm_nonneg ψ)
      _ ≤ δ * (‖ψ‖ + 1) :=
        mul_le_mul_of_nonneg_left hψLe hδ.le
      _ = ε / 8 := by
        dsimp [δ]
        have hψOne : ‖ψ‖ + 1 ≠ 0 := by positivity
        field_simp [hψOne]
        ring
      _ < ε / 4 := by linarith
  have hTriangle :
      ‖pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
          pvmBoundedBorelSpectralIntegralOperator P G ψ‖ ≤
        ‖pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
            pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK (F a)) ψ‖ +
          ‖pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK (F a)) ψ -
              pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK G) ψ‖ +
            ‖pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ -
                pvmBoundedBorelSpectralIntegralOperator P G ψ‖ := by
    calc
      ‖pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
          pvmBoundedBorelSpectralIntegralOperator P G ψ‖ =
        ‖(pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
            pvmBoundedBorelSpectralIntegralOperator P
              (pvmBoundedBorelRestrict K hK (F a)) ψ) +
          (pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK (F a)) ψ -
              pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK G) ψ) +
            (pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ -
                pvmBoundedBorelSpectralIntegralOperator P G ψ)‖ := by
              congr 1
              module
      _ ≤
          ‖(pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
              pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK (F a)) ψ) +
            (pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK (F a)) ψ -
                pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ)‖ +
            ‖pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ -
                pvmBoundedBorelSpectralIntegralOperator P G ψ‖ :=
        norm_add_le _ _
      _ ≤
          (‖pvmBoundedBorelSpectralIntegralOperator P (F a) ψ -
              pvmBoundedBorelSpectralIntegralOperator P
                (pvmBoundedBorelRestrict K hK (F a)) ψ‖ +
            ‖pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK (F a)) ψ -
                pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ‖) +
            ‖pvmBoundedBorelSpectralIntegralOperator P
                  (pvmBoundedBorelRestrict K hK G) ψ -
                pvmBoundedBorelSpectralIntegralOperator P G ψ‖ := by
          gcongr
          exact norm_add_le _ _
  exact hTriangle.trans_lt (by linarith)

/-- A semigroup spectral multiplier formula together with compact-uniform
convergence and integrated tail control at every physical vector. -/
structure EuclideanYangMillsOSPhysicalSpectralCompactTailDifferenceQuotient
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  quotientMultiplier :
    ℝ → PVMBoundedBorelRealFunction → PVMBoundedBorelRealFunction
  quotient_compactTail_tendsto :
    ∀ (f h : PVMBoundedBorelRealFunction),
      (∀ energy : ℝ, h.toFun energy = energy * f.toFun energy) →
      ∀ ψ : M.toExplicitModel.VacuumOrthogonalHilbert,
        PVMBoundedBorelCompactTailTendstoAtVector
          M.toExplicitModel.vacuumOrthogonalSpectralPVM
          (nhdsWithin 0 (Ioi 0))
          (fun t => quotientMultiplier t f) h ψ
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

/-- Compact/tail strong convergence and the semigroup spectral formula produce
the spectral right-Hamiltonian derivative package without global uniform
convergence on the full energy line. -/
noncomputable def EuclideanYangMillsOSPhysicalSpectralCompactTailDifferenceQuotient.toSpectralRightHamiltonianValue
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (D : EuclideanYangMillsOSPhysicalSpectralCompactTailDifferenceQuotient T) :
    EuclideanYangMillsOSPhysicalSpectralRightHamiltonianValue T where
  spectralIntegral_hasRightHamiltonianValue := by
    intro f h hCoordinate ψ
    unfold EuclideanYangMillsOSPhysicalTimeTranslation.HasRightHamiltonianValue
    have hSubtype :
        Tendsto
          (fun t =>
            M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              (D.quotientMultiplier t f) ψ)
          (nhdsWithin 0 (Ioi 0))
          (𝓝 (M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
            h ψ)) :=
      pvmBoundedBorelSpectralIntegralOperator_tendsto_atVector_of_compactTail
        M.toExplicitModel.vacuumOrthogonalSpectralPVM ψ
        (D.quotient_compactTail_tendsto f h hCoordinate ψ)
    have hAmbient :
        Tendsto
          (fun t =>
            ((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                (D.quotientMultiplier t f) ψ :
              M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H))
          (nhdsWithin 0 (Ioi 0))
          (𝓝 ((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
              h ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.toExplicitModel.H)) := by
      exact (continuous_subtype_val.tendsto _).comp hSubtype
    have hEventually :
        (fun t =>
          T.rightHamiltonianDifferenceQuotient
            ((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
                f ψ : M.toExplicitModel.VacuumOrthogonalHilbert) :
              M.toExplicitModel.H) t) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun t =>
          ((M.toExplicitModel.canonicalVacuumOrthogonalBoundedBorelSpectralIntegral
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
