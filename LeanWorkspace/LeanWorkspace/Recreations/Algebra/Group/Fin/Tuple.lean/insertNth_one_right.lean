import Mathlib

variable {n : ℕ} {α : Fin (n + 1) → Type*}

theorem insertNth_one_right [∀ j, One (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 1 = Pi.mulSingle i x := insertNth_eq_iff.2 <| by unfold removeNth; simp [succAbove_ne, Pi.one_def]

