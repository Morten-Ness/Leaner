import Mathlib

variable {M A B : Type*}

theorem IsScalarTower.of_mclosure_eq_top {N α} [Monoid M] [MulAction M N] [SMul N α] [MulAction M α]
    {s : Set M} (htop : Submonoid.closure s = ⊤)
    (hs : ∀ x ∈ s, ∀ (y : N) (z : α), (x • y) • z = x • y • z) : IsScalarTower M N α := by
  refine ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x ?_ ?_⟩
  · intro y z
    rw [one_smul, one_smul]
  · clear x
    intro x hx x' hx' y z
    rw [mul_smul, mul_smul, hs x hx, hx']

