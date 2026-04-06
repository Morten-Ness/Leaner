FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x)
    (f : ι → M) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  classical
  let e : s.attach ≃ Subtype p :=
    { toFun := fun x => ⟨x.1, (h x.1).mp x.2⟩
      invFun := fun y => ⟨⟨y.1, (h y.1).mpr y.2⟩, by simp⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }
  calc
    ∏ a ∈ s, f a = ∏ x in s.attach, f x.1 := by
      exact Finset.prod_attach s f
    _ = ∏ y : Subtype p, f y := by
      exact Finset.prod_bijective e (fun x => f x.1)
