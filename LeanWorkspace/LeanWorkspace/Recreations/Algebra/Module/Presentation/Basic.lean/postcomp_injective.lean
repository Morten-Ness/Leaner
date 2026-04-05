import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {solution : relations.Solution M} (h : solution.IsPresentation)

variable {N : Type v'} [AddCommGroup N] [Module A N]

theorem postcomp_injective {f f' : M →ₗ[A] N}
    (h' : solution.postcomp f = solution.postcomp f') : f = f' := by
  suffices f.comp solution.fromQuotient = f'.comp solution.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using Module.Relations.Solution.congr_var h' g

