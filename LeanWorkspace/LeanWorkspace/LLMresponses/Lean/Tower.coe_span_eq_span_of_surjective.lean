FAIL
import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s := by
  ext x
  constructor
  · intro hx
    exact Submodule.span_induction hx
      (fun y hy => Submodule.subset_span hy)
      (by simpa using (Submodule.zero_mem (Submodule.span R s)))
      (fun x y hx hy => Submodule.add_mem (Submodule.span R s) hx hy)
      (fun a x hx => by
        obtain ⟨r, rfl⟩ := h a
        simpa [smul_assoc] using Submodule.smul_mem (Submodule.span R s) r hx)
  · intro hx
    exact Submodule.span_mono (by
      intro y hy
      exact Submodule.subset_span hy) hx
