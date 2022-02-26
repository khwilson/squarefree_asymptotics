import algebra.squarefree

instance nat.decidable_is_unit : decidable_pred (@is_unit ℕ _) :=
begin
  intro x,
  exact decidable_of_iff _ nat.is_unit_iff.symm,
end

instance nat_sq : decidable_pred (λ x : ℕ, squarefree x) :=
begin
  intro n,
  by_cases hz : n = 0,
  { simp only [hz, not_squarefree_zero],
    exact decidable.false, },
  have : squarefree n ↔ (∀ x, x ≤ n → x * x ∣ n → is_unit x),
  { rw squarefree,
    apply forall_congr,
    intro x,
    split; intros hx,
    { intro h,
      exact hx, },
    intro h,
    apply hx _ h,
    have hl : x * x ≤ n,
    exact nat.le_of_dvd (zero_lt_iff.mpr hz) h,
    have : 1 ≤ x,
    { by_contra hn,
      simp only [not_le, nat.lt_one_iff] at hn,
      apply hz,
      simpa [hn] using h, },
    have h' : x * 1 ≤ x * x,
    refine mul_le_mul' (le_refl x) this,
    rw [mul_one] at h',
    exact h'.trans hl, },
  exact decidable_of_iff _ this.symm,
end

example : squarefree 130 := dec_trivial
