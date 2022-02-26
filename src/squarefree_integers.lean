import algebra.squarefree
import tactic

noncomputable theory
open_locale classical

def set_squarefree_le_x (N : ℕ): finset ℕ := finset.filter squarefree (finset.range (N + 1))

-- set_option trace.simplify.rewrite true

example : 1 ∈ (set_squarefree_le_x 1) :=
begin
  unfold set_squarefree_le_x,
  rw finset.mem_filter,
  split,
  {
    rw finset.mem_range,
    linarith,
  },
  {
    exact squarefree_one,
  },
end

lemma sq_0_eq_0 : finset.card (set_squarefree_le_x 0) = 0 :=
begin
  unfold set_squarefree_le_x,
  simp,
  rw finset.eq_empty_iff_forall_not_mem,
  intros x,
  rw finset.mem_filter,
  push_neg,
  intros h,
  rw finset.mem_singleton at h,
  rw h,
  exact not_squarefree_zero,
end

lemma sq_1_eq_1 : finset.card (set_squarefree_le_x 1) = 1 :=
begin
  unfold set_squarefree_le_x,
  rw finset.card_eq_succ,
  use 1,
  use ∅,
  split,
  simp,
  split,
  ext,
  have : 1 ∈ finset.filter squarefree (finset.range (1 + 1)) ∧ ∀ x ∈ finset.filter squarefree (finset.range (1 + 1)), x = 1, {
    split,
    rw finset.mem_filter,
    split,
    rw finset.mem_range,
    linarith,
    exact squarefree_one,
    intros x hx,
    rw finset.mem_filter at hx,
    rw finset.mem_range at hx,
    rcases hx with ⟨aa, bb⟩,
    by_contradiction H,
    have split_x : x < 1 ∨ x > 1, { exact ne.lt_or_lt H, },
    cases split_x,
    {
      have x_eq_0 : x = 0, {
        induction x,
        linarith,
        linarith,
      },
      rw x_eq_0 at bb,
      exact not_squarefree_zero bb,
    },
    {
      linarith [aa, split_x],
    },
  },
  rw ← finset.eq_singleton_iff_unique_mem at this,
  exact this,
  exact finset.card_empty,
end

lemma foo (n : ℕ) : n ∈ set_squarefree_le_x n ↔ squarefree n :=
begin
  split,
  intros hn,
  unfold set_squarefree_le_x at hn,
  rw finset.mem_filter at hn,
  exact hn.right,
  intros hn,
  unfold set_squarefree_le_x,
  rw finset.mem_filter,
  split,
  rw finset.mem_range,
  linarith,
  exact hn,
end

lemma sq_2_eq_2 : finset.card (set_squarefree_le_x 2) = 2 :=
begin
  unfold set_squarefree_le_x,
  rw finset.card_eq_succ,
  use 2,
  use set_squarefree_le_x 1,
  split,
  unfold set_squarefree_le_x,
  simp,
  split,
  conv {
    to_lhs,
    rw ← finset.mem_insert,
  },
  sorry,
  exact sq_1_eq_1,
end

-- example : finset.card (set_squarefree_le_x 5) = 4 :=
-- begin
--   unfold set_squarefree_le_x,
--   have a1 : 5 ∉ set_squarefree_le_x 4, {sorry,},
--   have a2 : set_squarefree_le_x 5 = finset.cons 5 (set_squarefree_le_x 4) a1, {sorry,},
--   let blah : (set_squarefree_le_x 5).to_list,

--   have eq_set : finset.filter squarefree (finset.range 6) = {1, 2, 3, 5}, {
--     sorry,
--   },
--   have eq_card : finset.card {1, 2, 3, 5} = 4, {
--     sorry,
--   },

-- end