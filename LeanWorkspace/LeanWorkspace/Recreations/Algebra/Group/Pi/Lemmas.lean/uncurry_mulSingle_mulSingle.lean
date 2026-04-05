import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem uncurry_mulSingle_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (a : α) (b : β a) (x : γ a b) :
    Sigma.uncurry (Pi.mulSingle a (Pi.mulSingle b x)) = Pi.mulSingle (Sigma.mk a b) x := by
  rw [← Sigma.curry_mulSingle ⟨a, b⟩, uncurry_curry]

