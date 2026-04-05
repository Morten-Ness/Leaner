import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBy_one : Submodule.torsionBy R M 1 = ⊥ := eq_bot_iff.mpr fun _ h => by
    rw [Submodule.mem_torsionBy_iff, one_smul] at h
    exact h

