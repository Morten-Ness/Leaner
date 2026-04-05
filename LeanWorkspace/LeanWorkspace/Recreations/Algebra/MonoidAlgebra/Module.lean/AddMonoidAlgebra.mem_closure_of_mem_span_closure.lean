import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S]

set_option backward.isDefEq.respectTransparency false in
theorem mem_closure_of_mem_span_closure [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
    (h : of' R M m ∈ Submodule.span R (Submonoid.closure <| of' R M '' s)) :
    m ∈ AddSubmonoid.closure s := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← h'] at h
  simpa using AddMonoidAlgebra.of'_mem_span.1 h

