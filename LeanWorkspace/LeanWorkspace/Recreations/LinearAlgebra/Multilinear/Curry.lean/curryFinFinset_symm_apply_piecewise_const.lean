import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem curryFinFinset_symm_apply_piecewise_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l)
    (f : MultilinearMap R (fun _ : Fin k => M') (MultilinearMap R (fun _ : Fin l => M') M₂))
    (x y : M') :
    (MultilinearMap.curryFinFinset R M₂ M' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) =
      f (fun _ => x) fun _ => y := by
  rw [MultilinearMap.curryFinFinset_symm_apply]; congr
  · ext
    rw [finSumEquivOfFinset_inl, Finset.piecewise_eq_of_mem]
    apply Finset.orderEmbOfFin_mem
  · ext
    rw [finSumEquivOfFinset_inr, Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ _ _)

