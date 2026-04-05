import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

variable (a a' : α → γ) (b b' : β → γ)

theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α → γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  ext j
  cases j with
  | inl a =>
      simp [Pi.mulSingle]
  | inr b =>
      by_cases h : b = i
      · subst h
        simp [Pi.mulSingle]
      · simp [Pi.mulSingle, h]
