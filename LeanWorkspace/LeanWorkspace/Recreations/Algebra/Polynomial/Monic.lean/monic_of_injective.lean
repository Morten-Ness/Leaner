import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R]

variable [Semiring S] {f : R →+* S}

theorem monic_of_injective (hf : Function.Injective f) {p : R[X]} (hp : (p.map f).Monic) : p.Monic := by
  apply hf
  rw [← leadingCoeff_map_of_injective hf, hp.leadingCoeff, f.map_one]

