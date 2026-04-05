import Mathlib

variable {G α β : Type*} [Group G]

variable [MulAction G α] {S : Subgroup G}

theorem mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

