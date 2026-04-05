import Mathlib

section

variable {n : ℕ} {α : Fin (n + 1) → Type*}

theorem insertNth_div_same [∀ j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSingle i (x / y) := by
  simp_rw [← Fin.insertNth_div, ← Fin.insertNth_one_right, Pi.div_def, div_self', Pi.one_def]

end
