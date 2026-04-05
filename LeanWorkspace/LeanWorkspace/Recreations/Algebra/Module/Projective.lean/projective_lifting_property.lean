import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem projective_lifting_property [h : Projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ h : P →ₗ[R] M, f ∘ₗ h = g := by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.linearCombination` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P →₀ R) →ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  obtain ⟨s, hs⟩ := h.out
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsuppSum]

