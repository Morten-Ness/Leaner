import Mathlib

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]

end

section

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

end

section

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

end

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

end

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

end

section

variable {α β : Type*} [Neg α]

theorem Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

end

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Odd.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β) :
    (r • g).Odd := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end

section

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.finset_sum_eq_zero [InvolutiveNeg α] {f : α → β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

end

section

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

end

section

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

end

section

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

end

section

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 := hf.finset_sum_eq_zero <| Finset.map_univ_equiv (Equiv.neg α)

end

section

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self, ← ho, he]

end
