import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (f : G →* N)

theorem map_eq_comap_of_inverse {f : G →* N} {g : N →* G} (hl : Function.LeftInverse g f)
    (hr : Function.RightInverse g f) (H : Subgroup G) : Subgroup.map f H = Subgroup.comap g H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g (f y) ∈ H
    simpa [hl y] using hy
  · intro hx
    refine ⟨g x, ?_, ?_⟩
    · exact hx
    · exact hr x
