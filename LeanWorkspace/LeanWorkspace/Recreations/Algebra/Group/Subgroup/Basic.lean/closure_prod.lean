import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem closure_prod {s : Set G} {t : Set N} (hs : 1 ∈ s) (ht : 1 ∈ t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) := le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (Subgroup.prod_le_iff.2 ⟨
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _x hx => subset_closure ⟨hx, ht⟩,
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

