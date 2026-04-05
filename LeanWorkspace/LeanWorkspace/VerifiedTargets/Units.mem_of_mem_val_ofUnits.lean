import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S := match hy with
  | ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

