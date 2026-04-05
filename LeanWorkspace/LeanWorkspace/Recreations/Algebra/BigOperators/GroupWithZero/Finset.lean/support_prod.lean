import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

variable [Nontrivial M₀] [NoZeroDivisors M₀]

theorem support_prod (s : Finset ι) (f : ι → κ → M₀) :
    support (fun j ↦ ∏ i ∈ s, f i j) = ⋂ i ∈ s, support (f i) := Set.ext fun x ↦ by simp [support, Finset.prod_eq_zero_iff]

