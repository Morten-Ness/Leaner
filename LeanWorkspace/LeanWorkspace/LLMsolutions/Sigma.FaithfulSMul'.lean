FAIL
import Mathlib

variable {ι : Type*} {M N : Type*} {α : ι → Type*}

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
by
  constructor
  intro m₁ m₂ h
  let f : α i → Σ j, α j := fun y => ⟨i, y⟩
  have hf : Function.Injective f := fun y₁ y₂ hxy => by simpa using Sigma.mk.inj_iff.mp hxy |>.2
  apply smul_left_cancel_of_nonzero ?_ ?_
  · intro y
    simpa [f] using h (f y)
  · exact fun h' => by
      apply hf
      simpa [f, h'] using h (f (Classical.choice (Classical.decEq (α i) |> fun _ => ⟨Classical.choice inferInstance⟩)))
