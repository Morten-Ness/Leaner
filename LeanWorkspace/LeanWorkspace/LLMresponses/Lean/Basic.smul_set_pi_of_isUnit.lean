FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem smul_set_pi_of_isUnit {M ι : Type*} {α : ι → Type*} [Monoid M] [∀ i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  rcases hc with ⟨u, rfl⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i hi
    exact ⟨y i, hy i hi, rfl⟩
  · intro hx
    refine ⟨fun i => ↑(u⁻¹) • x i, ?_, ?_⟩
    · intro i hi
      rcases hx i hi with ⟨yi, hyi, hyi'⟩
      change ↑(u⁻¹) • x i ∈ s i
      rw [← hyi']
      simpa only [Units.val_inv_eq_inv_val, smul_smul, Units.inv_mul, one_smul] using hyi
    · ext i
      change ↑u • (↑(u⁻¹) • x i) = x i
      simp only [Units.val_inv_eq_inv_val, smul_smul, Units.mul_inv, one_smul]
