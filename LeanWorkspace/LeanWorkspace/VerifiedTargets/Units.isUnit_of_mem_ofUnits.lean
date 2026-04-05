import Mathlib

variable {M : Type*} [Monoid M]

theorem isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (hx : x ∈ S.ofUnits) : IsUnit x := match hx with
  | ⟨_, _, h⟩ => ⟨_, h⟩

