import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 := by
  constructor
  · intro h x y hx hy hxy
    have hx' : x ∈ p₁ ⊓ p₂ := ⟨hx, hxy ▸ hy⟩
    have hx1 : x ∈ (⊥ : Submonoid M) := h.le_bot hx'
    exact hx1
  · intro h
    rw [disjoint_iff]
    ext x
    constructor
    · intro hx
      exact h hx.1 hx.2 rfl
    · intro hx
      exact Submonoid.mem_bot.mp hx |> fun hx1 => by simp [hx1]
