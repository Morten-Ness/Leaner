import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I]

theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_of_ne h.symm, h]

