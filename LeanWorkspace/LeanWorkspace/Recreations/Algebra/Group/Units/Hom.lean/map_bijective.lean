import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_bijective {f : M →* N} (hf : Function.Bijective f) : Function.Bijective <| Units.map f := by
  refine ⟨Units.map_injective hf.injective, ?_⟩
  rintro ⟨u, v, uv, vu⟩
  rcases hf.surjective u, hf.surjective v with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact ⟨⟨u, v, hf.injective <| by simpa, hf.injective <| by simpa⟩, rfl⟩

