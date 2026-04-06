FAIL
import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

variable {α : Type*} {β : α → Type*} {γ : ∀ a, β a → Type*}

theorem curry_mulSingle [DecidableEq α] [∀ a, DecidableEq (β a)] [∀ a b, One (γ a b)]
    (i : Σ a, β a) (x : γ i.1 i.2) :
    Sigma.curry (Pi.mulSingle i x) = Pi.mulSingle i.1 (Pi.mulSingle i.2 x) := by
  ext a b
  by_cases h₁ : a = i.1
  · subst h₁
    by_cases h₂ : HEq b i.2
    · cases h₂
      simp [Sigma.curry, Pi.mulSingle]
    · have hne : (Sigma.mk i.1 b : Sigma β) ≠ i := by
        intro h
        apply h₂
        cases h
        rfl
      simp [Sigma.curry, Pi.mulSingle, hne]
  · have hne : (Sigma.mk a b : Sigma β) ≠ i := by
      intro h
      apply h₁
      exact Sigma.mk.inj_1 h
    simp [Sigma.curry, Pi.mulSingle, h₁, hne]
