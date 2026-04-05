import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem addSubmonoid_closure_setOf_eq_monomial :
    AddSubmonoid.closure { p : R[X] | ∃ n a, p = Polynomial.monomial n a } = ⊤ := by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (Polynomial.toFinsuppIso R).symm.toAddEquiv, ←
    Finsupp.add_closure_setOf_eq_single, AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

