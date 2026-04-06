FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem center_prod {N : Type*} [Mul N] :
    Set.center (M × N) = Set.center M ×ˢ Set.center N := by
  ext x
  rcases x with ⟨m, n⟩
  constructor
  · intro hx
    rw [Set.mem_prod]
    constructor
    · rw [Set.mem_center_iff] at hx ⊢
      exact ⟨fun y => congrArg Prod.fst (hx (y, n))⟩
    · rw [Set.mem_center_iff] at hx ⊢
      exact ⟨fun y => congrArg Prod.snd (hx (m, y))⟩
  · intro hx
    rw [Set.mem_prod] at hx
    rcases hx with ⟨hm, hn⟩
    rw [Set.mem_center_iff] at hm hn ⊢
    exact ⟨fun y =>
      match y with
      | ⟨y₁, y₂⟩ =>
          by
            ext
            · exact hm.1 y₁
            · exact hn.1 y₂⟩
