import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem irreducible_mk {a : M} : Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [irreducible_iff, Associates.isUnit_mk, Associates.forall_associated, Associates.isUnit_mk, Associates.mk_mul_mk,
    Associates.mk_eq_mk_iff_associated, Associated.comm (x := a)]
  apply Iff.rfl.and
  constructor
  · rintro h x y Associated.rfl
    exact h _ _ <| .refl _
  · rintro h x y ⟨u, Associated.rfl⟩
    simpa using h (mul_assoc _ _ _)

