import algebra.squarefree
import tactic

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

def set_squarefree_le_x (N : ℕ) : list ℕ := (list.range (N + 1)).filter squarefree

lemma list_eq_singleton_iff_length (l : list ℕ) (n : ℕ) : l = [n] ↔ l.length = 1 ∧ n ∈ l :=
begin
  split,
  intros h,
  split,
  simp [list.length_singleton, h],
  simp [list.mem_singleton, h],
  rintros ⟨hl_length, hl_contains⟩,
  rw list.length_eq_one at hl_length,
  cases hl_length with a ha,
  rw [ha, list.mem_singleton] at hl_contains,
  rw ha,
  simp,
  rw hl_contains,
end

lemma filter_singleton_eq_iff (N : ℕ) (p : ℕ → Prop) [decidable_pred p] : list.filter p [N] = [N] ↔ p N :=
begin
  rw list_eq_singleton_iff_length,
  split,
  {
    rintros ⟨_, N_in_filter⟩,
    rw list.mem_filter at N_in_filter,
    exact N_in_filter.right,
  },
  {
    intros h,
    have second_goal : N ∈ list.filter p [N], {
      rw list.mem_filter,
      simp,
      exact h,
    },
    split,
    have pos_length : 0 < (list.filter p [N]).length, {
      rw list.length_pos_iff_exists_mem,
      use N,
      exact second_goal,
    },
    have length_at_most_one : (list.filter p [N]).length ≤ 1, {
      calc
        (list.filter p [N]).length ≤ [N].length : by {rw ← list.countp_eq_length_filter p, exact list.countp_le_length p,}
          ... = 1 : list.length_singleton N,
    },
    linarith,
    exact second_goal,
  }
end

lemma append_right_eq_implies_nil (a b: list ℕ) : a ++ b = a ↔ b = list.nil :=
begin
  conv {
    to_lhs,
    to_rhs,
    rw ← list.append_nil a,
  },
  split,
  intros h,
  exact list.append_left_cancel h,
  intros h,
  rw h,
end

lemma filter_range_succ_eq_iff (N : ℕ) (p : ℕ → Prop) [decidable_pred p] : list.filter p (list.range (N + 1)) = list.filter p (list.range N) ↔ ¬ p N :=
begin
  rw list.range_succ N,
  rw list.filter_append,
  rw append_right_eq_implies_nil,
  rw list.eq_nil_iff_forall_not_mem,

  split,
  {
    intros h,
    specialize h N,
    rw list.mem_filter at h,
    push_neg at h,
    specialize h (list.mem_singleton_self N),
    exact h,
  },
  {
    intros h a,
    rw list.mem_filter,
    push_neg,
    intros ha,
    rw list.mem_singleton at ha,
    rw ha,
    exact h,
  },
end

lemma filter_range_succ_neq_iff (N : ℕ) (p : ℕ → Prop) [decidable_pred p] : list.filter p (list.range (N + 1)) = list.filter p (list.range N) ++ [N] ↔ p N :=
begin
  rw list.range_succ N,
  rw list.filter_append,
  split,
  {
    intros h,
    rw ← filter_singleton_eq_iff N p,
    rw ← list.append_right_inj,
    exact h,
  },
  {
    intros h,
    rw list.append_right_inj,
    rw filter_singleton_eq_iff N p,
    exact h,
  },
end

lemma val_0 : set_squarefree_le_x 0 = [] :=
begin
  unfold set_squarefree_le_x,
  rw list.eq_nil_iff_forall_not_mem,
  intros n,
  rw list.mem_filter,
  push_neg,
  intros hn,
  rw list.mem_range at hn,
  have : n = 0, { linarith, },
  rw this,
  exact not_squarefree_zero,
end

lemma val_1 : set_squarefree_le_x 1 = [1] :=
begin
  unfold set_squarefree_le_x,
  norm_num,
  have : set_squarefree_le_x 1 = set_squarefree_le_x 0 ++ [1], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_0 at this,
  tauto,
end


lemma val_2 : set_squarefree_le_x 2 = [1, 2] :=
begin
  have : set_squarefree_le_x 2 = set_squarefree_le_x 1 ++ [2], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_1 at this,
  tauto,
end

lemma val_3 : set_squarefree_le_x 3 = [1, 2, 3] :=
begin
  have : set_squarefree_le_x 3 = set_squarefree_le_x 2 ++ [3], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_2 at this,
  tauto,
end

lemma val_4 : set_squarefree_le_x 4 = [1, 2, 3] :=
begin
  have : set_squarefree_le_x 4 = set_squarefree_le_x 3, {
    unfold set_squarefree_le_x,
    rw filter_range_succ_eq_iff,
    dec_trivial,
  },
  rw val_3 at this,
  tauto,
end

lemma val_5 : set_squarefree_le_x 5 = [1, 2, 3, 5] :=
begin
  have : set_squarefree_le_x 5 = set_squarefree_le_x 4 ++ [5], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_4 at this,
  tauto,
end

lemma val_6 : set_squarefree_le_x 6 = [1, 2, 3, 5, 6] :=
begin
  have : set_squarefree_le_x 6 = set_squarefree_le_x 5 ++ [6], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_5 at this,
  tauto,
end

lemma val_7 : set_squarefree_le_x 7 = [1, 2, 3, 5, 6, 7] :=
begin
  have : set_squarefree_le_x 7 = set_squarefree_le_x 6 ++ [7], {
    unfold set_squarefree_le_x,
    rw filter_range_succ_neq_iff,
    dec_trivial,
  },
  rw val_6 at this,
  tauto,
end

lemma val_8 : set_squarefree_le_x 8 = [1, 2, 3, 5, 6, 7] :=
begin
  have : set_squarefree_le_x 8 = set_squarefree_le_x 7, {
    unfold set_squarefree_le_x,
    rw filter_range_succ_eq_iff,
    dec_trivial,
  },
  rw val_7 at this,
  tauto,
end

lemma val_9 : set_squarefree_le_x 9 = [1, 2, 3, 5, 6, 7] :=
begin
  have : set_squarefree_le_x 9 = set_squarefree_le_x 8, {
    unfold set_squarefree_le_x,
    rw filter_range_succ_eq_iff,
    dec_trivial,
  },
  rw val_8 at this,
  tauto,
end
