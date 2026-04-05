import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem mul_prod_eraseIdx {i} (hlen : i < l.length) (hcomm : ∀ a' ∈ l.take i, Commute l[i] a') :
    l[i] * (l.eraseIdx i).prod = l.prod := by
  rw [← List.prod_insertIdx (by grind : i ≤ (l.eraseIdx i).length) (fun a' a'_mem =>
      hcomm a' (by rwa [take_eraseIdx_eq_take_of_le l i i (Nat.le_refl i)] at a'_mem)),
    insertIdx_eraseIdx_getElem hlen]

