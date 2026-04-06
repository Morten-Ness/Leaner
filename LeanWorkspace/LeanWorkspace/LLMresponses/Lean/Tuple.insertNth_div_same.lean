FAIL
import Mathlib

variable {n : ℕ} {α : Fin (n + 1) → Type*}

theorem insertNth_div_same [∀ j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSingle i (x / y) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [Pi.mulSingle]
  · have hx : i.insertNth x p j = i.insertNth y p j := by
      simp [Fin.insertNth, h]
    rw [Pi.div_apply, hx, div_self]
    · simp [Pi.mulSingle, h]
    · exact i.insertNth y p j
