import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisors_dvd_iff_dvd_coe {a b : M₀⁰} :
    a ∣ b ↔ (a : M₀) ∣ (b : M₀) := ⟨fun ⟨c, hc⟩ ↦ by simp_rw [hc, Submonoid.coe_mul, dvd_mul_right],
  fun ⟨c, hc⟩ ↦ ⟨⟨c, (mul_mem_nonZeroDivisors.mp (hc ▸ b.prop)).2⟩,
    by simp_rw [Subtype.ext_iff, Submonoid.coe_mul, hc]⟩⟩

