import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_map_equiv {f : G ≃* N} {K : Subgroup G} {x : N} :
    x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K := Set.mem_image_equiv

-- The simpNF linter says that the LHS can be simplified via `Subgroup.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207

