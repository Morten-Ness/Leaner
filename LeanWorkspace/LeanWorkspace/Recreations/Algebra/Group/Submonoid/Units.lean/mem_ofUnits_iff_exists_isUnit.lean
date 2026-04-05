import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S := ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
  fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

