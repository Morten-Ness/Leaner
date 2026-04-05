import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable (solution : relations.Solution M)

theorem injective_fromQuotient_iff_ker_π_eq_span :
    Function.Injective solution.fromQuotient ↔
      LinearMap.ker solution.π = Submodule.span A (Set.range relations.relation) := by
  constructor
  · intro h
    rw [← Module.Relations.ker_toQuotient, ← Module.Relations.Solution.fromQuotient_comp_toQuotient, LinearMap.ker_comp,
      LinearMap.ker_eq_bot.2 h, Submodule.comap_bot]
  · intro h
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨x, rfl⟩ := Module.Relations.surjective_toQuotient relations x
    replace hx : x ∈ LinearMap.ker solution.π := by
      simpa only [LinearMap.mem_ker, Module.Relations.Solution.fromQuotient_toQuotient] using hx
    rw [h, ← Module.Relations.range_map] at hx
    obtain ⟨x, rfl⟩ := hx
    simp only [Module.Relations.toQuotient_map_apply, Submodule.zero_mem]

