import Mathlib

section

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem curry_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  simp only [Pi.mulSingle, Sigma.curry_update, Sigma.curry_one, Pi.one_apply]

end

section

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

theorem mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
    (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x := by
  ext x
  aesop (add simp Pi.mulSingle_apply)

end
