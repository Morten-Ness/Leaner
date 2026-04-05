import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

variable [RingHomSurjective τ₁₂]

theorem range_eq_ker_of_leftInverse {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M →ₗ[R] P} {g : P →ₗ[R] M}
    (h : LeftInverse g f) : f.range = ker ((f.comp g) - LinearMap.id) := -- If `y = f x ∈ LinearMap.range f`, we have `(f ∘ g) y = f (g (f x)) = f x = y` by hypothesis `h`.
  -- Conversely, f g z - z = 0 implies z = f (g z) ∈ LinearMap.range f.
  le_antisymm (by rintro y ⟨x, rfl⟩; simp [h x]) (fun x hx ↦ ⟨g x, by simpa [sub_eq_zero] using hx⟩)

