import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem even_iff_two_dvd : Even a ↔ 2 ∣ a := by simp [Even, Dvd.dvd, two_mul]

alias ⟨Even.two_dvd, _⟩ := even_iff_two_dvd

