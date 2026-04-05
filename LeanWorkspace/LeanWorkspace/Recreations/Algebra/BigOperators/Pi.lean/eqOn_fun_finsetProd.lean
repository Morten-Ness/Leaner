import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem eqOn_fun_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (fun b ↦ ∏ i ∈ v, f i b) (fun b ↦ ∏ i ∈ v, f' i b) s := by
  convert eqOn_finsetProd h v <;> simp

