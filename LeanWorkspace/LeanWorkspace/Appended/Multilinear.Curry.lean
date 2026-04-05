import Mathlib

section

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

theorem MultilinearMap.curry_uncurryRight
    (f : MultilinearMap R (fun i : Fin n => M (castSucc i)) (M (last n) →ₗ[R] M₂)) :
    f.uncurryRight.curryRight = f := by
  ext m x
  simp only [snoc_last, MultilinearMap.curryRight_apply, MultilinearMap.uncurryRight_apply]
  rw [init_snoc]

end

section

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem coe_currySumEquiv : ⇑(MultilinearMap.currySumEquiv (R := R) (N := N) (M₂ := M₂)) = MultilinearMap.currySum :=
  rfl

end

section

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem coe_currySumEquiv_symm : ⇑(MultilinearMap.currySumEquiv (R := R) (N := N) (M₂ := M₂)).symm = MultilinearMap.uncurrySum :=
  rfl

end

section

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem curryFinFinset_apply_const {k l n : ℕ} {s : Finset (Fin n)} (hk : #s = k)
    (hl : #sᶜ = l) (f : MultilinearMap R (fun _ : Fin n => M') M₂) (x y : M') :
    (MultilinearMap.curryFinFinset R M₂ M' hk hl f (fun _ => x) fun _ => y) =
      f (s.piecewise (fun _ => x) fun _ => y) := by
  rw [← MultilinearMap.curryFinFinset_symm_apply_piecewise_const hk hl, LinearEquiv.symm_apply_apply]

end

section

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

end

section

variable {R : Type uR} {S : Type uS} {ι : Type uι} {ι' : Type uι'} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₂ : Type v₂} {M₃ : Type v₃} {M' : Type v'}

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [AddCommMonoid M'] [AddCommMonoid M₂]
  [∀ i, Module R (M i)] [Module R M'] [Module R M₂]

variable {R M₂} {N : (ι ⊕ ι') → Type*}
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

theorem uncurrySum_currySum (f : MultilinearMap R N M₂) :
    MultilinearMap.uncurrySum (MultilinearMap.currySum f) = f := by
  ext
  simp only [MultilinearMap.uncurrySum_apply, MultilinearMap.currySum_apply]
  congr
  ext (_ | _) <;> simp

end
