import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem isPrimal_mk {a : M} : IsPrimal (Associates.mk a) ↔ IsPrimal a := by
  simp_rw [IsPrimal, Associates.forall_associated, Associates.mk_surjective.exists, Associates.mk_mul_mk, Associates.mk_dvd_mk]
  constructor <;> intro h b c dvd <;> obtain ⟨a₁, a₂, h₁, h₂, eq⟩ := @h b c dvd
  · obtain ⟨u, Associated.rfl⟩ := Associates.mk_eq_mk_iff_associated.mp Associated.symm eq
    exact ⟨a₁, a₂ * u, h₁, Units.mul_right_dvd.mpr h₂, mul_assoc _ _ _⟩
  · exact ⟨a₁, a₂, h₁, h₂, congr_arg _ eq⟩

