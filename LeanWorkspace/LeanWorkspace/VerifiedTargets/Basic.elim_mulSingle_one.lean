import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

variable (a a' : α → γ) (b b' : β → γ)

theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, Sum.elim_one_one]

