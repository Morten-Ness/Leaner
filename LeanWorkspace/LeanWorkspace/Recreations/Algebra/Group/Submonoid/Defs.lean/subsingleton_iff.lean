import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M := ⟨fun _ =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        Submonoid.mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ Submonoid.mem_top i
      (this x).trans (this y).symm⟩,
    fun _ ↦ ⟨fun x y ↦ Submonoid.ext fun i ↦ by simp [← Subsingleton.elim 1 i]⟩⟩

