import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_isTorsionBySet : IsTorsionBySet R (Submodule.torsionBySet R M s) s := fun ⟨_, hx⟩ a => Subtype.ext <| (Submodule.mem_torsionBySet_iff _ _).mp hx a

