import Mathlib

variable {M : Type*} [Monoid M]

theorem Subgroup.units_ofUnits_eq (S : Subgroup Mˣ) : S.ofUnits.units = S := Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, _, S.inv_mem hm, rfl⟩⟩)

