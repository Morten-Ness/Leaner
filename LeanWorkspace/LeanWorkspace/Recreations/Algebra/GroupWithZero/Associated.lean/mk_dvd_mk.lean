import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b := by
  simp only [dvd_def, Associates.mk_surjective.exists, Associates.mk_mul_mk, Associates.mk_eq_mk_iff_associated,
    Associated.comm (x := b)]
  constructor
  · rintro ⟨x, u, Associated.rfl⟩
    exact ⟨_, mul_assoc ..⟩
  · rintro ⟨c, Associated.rfl⟩
    use c

