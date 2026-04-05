import Mathlib

variable {M : Type*}

theorem associated_zero_iff_eq_zero [MonoidWithZero M] (a : M) : a ~ᵤ 0 ↔ a = 0 := Iff.intro
    (fun h => by
      let ⟨u, h⟩ := Associated.symm h
      simpa using Associated.symm h)
    fun h => h ▸ Associated.refl a

