import MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For any compact plaquette construction data, compact support transports from
`constructObservable chosenPlaquette` to `chosenObservable` using the defining
chosen-observable equality. -/
theorem compact_plaquette_chosen_compact_support
    (D : CompactPlaquetteConstructionTheoremData) :
    D.compactSupport D.chosenObservable := by
  rw [D.chosenObservable_def]
  exact D.constructed_compactSupport

/-- For any compact plaquette construction data, centeredness transports from
`constructObservable chosenPlaquette` to `chosenObservable` using the defining
chosen-observable equality. -/
theorem compact_plaquette_chosen_centered
    (D : CompactPlaquetteConstructionTheoremData) :
    D.centered D.chosenObservable := by
  rw [D.chosenObservable_def]
  exact D.constructed_centered

/-- For any compact plaquette construction data, smearing transports from
`constructObservable chosenPlaquette` to `chosenObservable` using the defining
chosen-observable equality. -/
theorem compact_plaquette_chosen_smeared
    (D : CompactPlaquetteConstructionTheoremData) :
    D.smeared D.chosenObservable := by
  rw [D.chosenObservable_def]
  exact D.constructed_smeared

/-- The same compact-support transport, but using only the `ready` package. -/
theorem compact_plaquette_ready_chosen_compact_support
    (D : CompactPlaquetteConstructionTheoremData)
    (hD : D.ready) :
    D.compactSupport D.chosenObservable := by
  rcases hD with ⟨_, hdef, hcompact, _, _, _, _, _⟩
  rw [hdef]
  exact hcompact

/-- The same centeredness transport, but using only the `ready` package. -/
theorem compact_plaquette_ready_chosen_centered
    (D : CompactPlaquetteConstructionTheoremData)
    (hD : D.ready) :
    D.centered D.chosenObservable := by
  rcases hD with ⟨_, hdef, _, hcentered, _, _, _, _⟩
  rw [hdef]
  exact hcentered

/-- The same smearing transport, but using only the `ready` package. -/
theorem compact_plaquette_ready_chosen_smeared
    (D : CompactPlaquetteConstructionTheoremData)
    (hD : D.ready) :
    D.smeared D.chosenObservable := by
  rcases hD with ⟨_, hdef, _, _, hsmeared, _, _, _⟩
  rw [hdef]
  exact hsmeared

/-- Singleton compact support for the chosen observable. -/
theorem singleton_compact_plaquette_chosen_compact_support :
    singletonCompactPlaquetteConstructionTheoremData.compactSupport
      singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_plaquette_chosen_compact_support
    singletonCompactPlaquetteConstructionTheoremData

/-- Singleton centeredness for the chosen observable. -/
theorem singleton_compact_plaquette_chosen_centered :
    singletonCompactPlaquetteConstructionTheoremData.centered
      singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_plaquette_chosen_centered
    singletonCompactPlaquetteConstructionTheoremData

/-- Singleton smearing for the chosen observable. -/
theorem singleton_compact_plaquette_chosen_smeared :
    singletonCompactPlaquetteConstructionTheoremData.smeared
      singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_plaquette_chosen_smeared
    singletonCompactPlaquetteConstructionTheoremData

end

end MathlibAnalytic
end MGAP4D
