import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_isUnit_iff {M : Type*} [CommMonoid M] {L : List M} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by
  refine ⟨fun h => ?_, List.prod_isUnit⟩
  induction L with
  | nil => exact fun m' h' => False.elim (not_mem_nil h')
  | cons m L ih =>
    rw [prod_cons, IsUnit.mul_iff] at h
    exact fun m' h' ↦ Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H

