FAIL
import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable [DecidableEq I] [∀ i, Preorder (f i)] [∀ i, One (f i)]

theorem mulSingle_comp_equiv {m n : Type*} [DecidableEq n] [DecidableEq m] [One α] (σ : n ≃ m)
    (i : m) (x : α) : Pi.mulSingle i x ∘ σ = Pi.mulSingle (σ.symm i) x := by
  ext j
  by_cases h : j = σ.symm i
  · subst h
    simp [Pi.mulSingle]
  · simp [Pi.mulSingle, h]
    intro h'
    apply h
    exact σ.injective (by simpa using h')
