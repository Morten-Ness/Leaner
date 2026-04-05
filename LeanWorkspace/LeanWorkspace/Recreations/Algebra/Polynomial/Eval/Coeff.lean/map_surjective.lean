import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := fun p =>
  p.induction_on'
    (by rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩; exact ⟨p + q, Polynomial.map_add f⟩)
    fun n s ↦
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩

