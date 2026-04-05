import Mathlib

variable {n : ℕ} {α : Fin (n + 1) → Type*}

theorem insertNth_mul [∀ j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q := insertNth_binop (fun _ ↦ (· * ·)) i x y p q

