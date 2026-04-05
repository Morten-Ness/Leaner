import Mathlib

section

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit

end

section

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_bijective {f : M →* N} (hf : Function.Bijective f) : Function.Bijective <| Units.map f := by
  refine ⟨Units.map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact ⟨⟨u, v, hf.injective <| by simpa, hf.injective <| by simpa⟩, rfl⟩

end
