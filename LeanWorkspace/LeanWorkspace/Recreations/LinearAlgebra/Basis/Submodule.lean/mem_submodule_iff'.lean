import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

theorem mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Module.Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : M) := Module.Basis.mem_submodule_iff b.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

