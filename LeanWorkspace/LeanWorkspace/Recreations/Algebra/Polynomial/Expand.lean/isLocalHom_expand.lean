import Mathlib

variable (R : Type u) [CommRing R] [IsDomain R]

theorem isLocalHom_expand {p : ℕ} (hp : 0 < p) : IsLocalHom (Polynomial.expand R p) := by
  refine ⟨fun f hf1 => ?_⟩
  have hf2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit hf1)
  rw [Polynomial.coeff_expand hp, if_pos (dvd_zero _), p.zero_div] at hf2
  rw [hf2, isUnit_C] at hf1; rw [Polynomial.expand_eq_C hp] at hf2; rwa [hf2, isUnit_C]

