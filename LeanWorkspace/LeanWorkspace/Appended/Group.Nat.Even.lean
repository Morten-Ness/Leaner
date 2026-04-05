import Mathlib

section

variable {m n : ℕ}

theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by grind

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, parity_simps]

example : ¬Even 25394535 := by decide

end

section

variable {m n : ℕ}

theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n := fun h ↦ Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

end

section

variable {m n : ℕ}

theorem even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

end

section

variable {m n : ℕ}

theorem two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h ↦
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)

end
