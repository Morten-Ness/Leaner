import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_bijective {f : M →* N} (hf : Function.Bijective f) : Function.Bijective <| Units.map f := by
  rcases hf with ⟨hf_inj, hf_surj⟩
  constructor
  · intro u v h
    apply Units.ext
    apply hf_inj
    exact congrArg Units.val h
  · intro u
    rcases hf_surj (u : N) with ⟨x, hx⟩
    rcases hf_surj ((↑(u⁻¹)) : N) with ⟨y, hy⟩
    refine ⟨⟨x, y, ?_, ?_⟩, ?_⟩
    · apply hf_inj
      rw [map_mul, hx, hy]
      simpa using u.mul_inv
    · apply hf_inj
      rw [map_mul, hy, hx]
      simpa using u.inv_mul
    · apply Units.ext
      exact hx
