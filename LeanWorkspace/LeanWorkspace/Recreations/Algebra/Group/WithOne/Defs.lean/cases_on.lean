import Mathlib

variable {α : Type u}

theorem cases_on {P : WithOne α → Prop} : ∀ x : WithOne α, P 1 → (∀ a : α, P a) → P x := Option.casesOn

