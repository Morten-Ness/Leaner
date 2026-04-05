import Mathlib

variable {R : Type u} {M : Type v}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem basis_finite_of_finite_spans [Nontrivial R] {s : Set M} (hs : s.Finite)
    (hsspan : span R s = ⊤) {ι : Type w} (b : Basis ι R M) : Finite ι := by
  have := congr(($hsspan).map b.repr.toLinearMap)
  rw [← span_image, Submodule.map_top, LinearEquiv.range] at this
  exact finite_of_span_finite_eq_top_finsupp (hs.image _) this

