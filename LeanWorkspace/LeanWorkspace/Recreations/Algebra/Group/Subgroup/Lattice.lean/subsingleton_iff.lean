import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem subsingleton_iff : Subsingleton (Subgroup G) ↔ Subsingleton G := ⟨fun _ =>
    ⟨fun x y =>
      have : ∀ i : G, i = 1 := fun i =>
        Subgroup.mem_bot.mp <| Subsingleton.elim (⊤ : Subgroup G) ⊥ ▸ Subgroup.mem_top i
      (this x).trans (this y).symm⟩,
    fun _ => ⟨fun x y => Subgroup.ext fun i => Subsingleton.elim 1 i ▸ by simp⟩⟩

