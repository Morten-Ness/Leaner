import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 := Submonoid.disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx <| hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

