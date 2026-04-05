import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem isInternal_biSup_submodule_of_iSupIndep {A : ι → Submodule R M} (s : Set ι)
    (h : iSupIndep <| fun i : s ↦ A i) :
    IsInternal <| fun (i : s) ↦ (A i).comap (⨆ i ∈ s, A i).subtype := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i ∈ s, A i
  have hp : ∀ i ∈ s, A i ≤ p := fun i hi ↦ le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s ↦ (A i).comap p.subtype) = fun i ↦ ⟨A i, hp i i.property⟩ by
    rw [← iSupIndep_map_orderIso_iff e, this]
    exact .of_coe_Iic_comp h
  ext i m
  change m ∈ ((A i).comap p.subtype).map p.subtype ↔ _
  rw [Submodule.map_comap_subtype, inf_of_le_right (hp i i.property)]

