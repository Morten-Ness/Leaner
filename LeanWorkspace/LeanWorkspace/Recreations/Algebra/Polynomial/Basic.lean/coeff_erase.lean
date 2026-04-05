import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_erase (p : R[X]) (n i : ℕ) :
    (p.erase n).coeff i = if i = n then 0 else p.coeff i := by
  rcases p with ⟨⟩
  simp only [erase_def, Polynomial.coeff]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

