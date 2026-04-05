import Mathlib

variable {S M G : Type*}

variable [Semigroup S] {a b x y z x' y' : S}

theorem isTrans : IsTrans S fun a b ↦ ∃ c, SemiconjBy c a b := ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨y * x, SemiconjBy.mul_left hy hx⟩⟩

