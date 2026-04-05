import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_eq_quasiIso_map_quotient :
    HomotopyCategory.quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
    exact ((HomotopyCategory.quasiIso C c).arrow_mk_iso_iff e).1 h

