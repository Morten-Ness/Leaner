import Mathlib

variable {α M : Type*} [CommMonoid M]

theorem prod_eraseNone (f : α → M) (s : Finset (Option α)) :
    ∏ x ∈ eraseNone s, f x = ∏ x ∈ s, Option.elim' 1 f x := by
  classical calc
      ∏ x ∈ eraseNone s, f x = ∏ x ∈ (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x ∈ s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x ∈ s, Option.elim' 1 f x := prod_erase _ rfl

