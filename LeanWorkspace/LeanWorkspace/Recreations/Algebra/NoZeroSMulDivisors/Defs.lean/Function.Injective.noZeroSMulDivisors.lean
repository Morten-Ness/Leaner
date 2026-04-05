import Mathlib

variable {R M G : Type*}

theorem Function.Injective.noZeroSMulDivisors {R M N : Type*} [Zero R] [Zero M] [Zero N]
    [SMul R M] [SMul R N] [NoZeroSMulDivisors R N] (f : M → N) (hf : Function.Injective f)
    (h0 : f 0 = 0) (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSMulDivisors R M := ⟨fun {_ _} h =>
    Or.imp_right (@hf _ _) <| h0.symm ▸ eq_zero_or_eq_zero_of_smul_eq_zero (by rw [← hs, h, h0])⟩

-- See note [lower instance priority]

