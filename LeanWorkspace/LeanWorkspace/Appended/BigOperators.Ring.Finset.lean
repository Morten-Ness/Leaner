import Mathlib

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalSemiring R] {f : ι → R} {a : R}

theorem dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i := Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem mul_sum (s : Finset ι) (f : ι → R) (a : R) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := map_sum (AddMonoidHom.mulLeft a) _ s

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem prod_one_add_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 + f j) := by
  rw [Finset.prod_add_ordered]
  simp

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 - f j) := by
  rw [Finset.prod_sub_ordered]
  simp

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j - g j)) * ∏ j ∈ s with i < j, f j := by
  simp only [sub_eq_add_neg]
  convert Finset.prod_add_ordered s f fun i => -g i
  simp

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem sum_mul (s : Finset ι) (f : ι → R) (a : R) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s

end

section

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j := by
  simp_rw [Finset.sum_mul, ← Finset.mul_sum]

end
