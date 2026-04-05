import Mathlib

variable {ι β : Type*}

variable [CommMonoid β]

theorem prod_univ_pi [DecidableEq ι] [Fintype ι] {κ : ι → Type*} (t : ∀ i, Finset (κ i))
    (f : (∀ i ∈ (univ : Finset ι), κ i) → β) :
    ∏ x ∈ univ.pi t, f x = ∏ x ∈ Fintype.piFinset t, f fun a _ ↦ x a := by
  apply prod_nbij' (fun x i ↦ x i <| mem_univ _) (fun x i _ ↦ x i) <;> simp

