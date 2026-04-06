FAIL
import Mathlib

variable {M α β : Type*} (e : α ≃ β)

theorem div_def [Div β] (x y : α) :
    let _ : Div α := ⟨fun a b => e.symm (e a / e b)⟩
    e (x / y) = e x / e y := by
  dsimp
