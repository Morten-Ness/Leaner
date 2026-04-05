import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] :
    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ ↦ zero_ne_one (H.symm.trans (one_pow _))

