import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem mk_dvdNotUnit_mk_iff {a b : M} :
    DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b := by
  simp only [DvdNotUnit, Associates.mk_ne_zero, Associates.mk_surjective.exists, Associates.isUnit_mk, Associates.mk_mul_mk,
    Associates.mk_eq_mk_iff_associated, Associated.comm (x := b)]
  refine Iff.rfl.and ?_
  constructor
  · rintro ⟨x, hx, u, Associated.rfl⟩
    refine ⟨x * u, ?_, mul_assoc ..⟩
    simpa
  · rintro ⟨x, ⟨hx, Associated.rfl⟩⟩
    use x

