import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

lemma two_add {n : ℕ} (hn : 2 ≤ n) : ∃ n', n = 2 + n' :=
begin
  have : n - 2 + 2 = n, apply nat.sub_add_cancel hn,
  use n - 2,
  ring_nf,
  exact this.symm,
end

lemma two_le_nat_iff_not_zero_one {m : ℕ} : 2 ≤ m ↔ m ≠ 0 ∧ m ≠ 1 :=
begin
  split,
  intros h,
  split,
  linarith,
  linarith,
  rintros ⟨h, hh⟩,
  induction m,
  simp [h],
  exact h rfl,
  induction m_n,
  exfalso,
  exact hh rfl,

  calc m_n_n.succ.succ = m_n_n.succ + 1 : rfl
    ... = m_n_n + 1 + 1 : rfl
    ... = m_n_n + 2 : by ring
    ... ≥ 0 + 2 : le_add_self
    ... = 2 : by ring,
end

lemma pow_not_squarefree : ∀ (p i : ℕ), 2 ≤ p → 2 ≤ i → ¬squarefree (p^i) :=
begin
  intros p i hp hi,
  have : p * p ∣ p^i, {
    obtain ⟨i', hi'⟩ : ∃ i', i = 2 + i', exact two_add hi,
    rw hi',
    rw pow_add,
    rw pow_two,
    exact dvd_mul_right (p * p) (p ^ i'),
  },
  by_contradiction H,
  unfold squarefree at H,
  specialize H p this,
  simp at H,
  linarith,
end

lemma lt_of_div {a b : ℕ} (hb : 2 ≤ b) : a ≠ 0 → a / b < a :=
begin
  contrapose!,
  intros h,
  exact nat.eq_zero_of_le_div hb h,
end

lemma has_coprime_part_strong : ∀ (M m p : ℕ), m ≤ M → 1 ≤ m → nat.prime p → ∃ (m' i : ℕ), m = (p^i) * m' ∧ p.coprime m' :=
begin
  intros M,
  induction M with M hM,
  simp,
  intros m p hm hm',
  linarith,
  intros m p hm_ind one_le_m hp,
  have m_ne_zero : m ≠ 0, linarith,
  have zero_lt_m : 0 < m, linarith,
  by_cases p_dvd_m : p ∣ m,
  {
    have p_le_m : p ≤ m, exact nat.le_of_dvd zero_lt_m p_dvd_m,
    have mdp_ne_zero : m / p ≠ 0, {
      by_contradiction H,
      have : p * (m / p) = 0,
        calc p * (m / p) = p * 0 : by simp [H]
          ... = 0 : by simp,
      rw @nat.mul_div_cancel_left' p m p_dvd_m at this,
      exact m_ne_zero this,
    },
    have : 2 ≤ p, exact nat.prime.two_le hp,
    have : m / p < M.succ,
      calc m / p < m : lt_of_div this m_ne_zero
        ... ≤ M.succ : hm_ind,
    have aaa : m / p ≤ M, exact lt_succ_iff.mp this,
    have bbb : 1 ≤ m / p, exact zero_lt_iff.mpr mdp_ne_zero,
    rcases hM (m / p) p aaa bbb hp with ⟨m', i', hm', hmp'⟩,
    use m',
    use i' + 1,
    split,
    conv {
      to_rhs,
      rw pow_add,
      congr,
      rw mul_comm,
    },
    conv {
      to_rhs,
      rw mul_assoc,
    },
    rw ← hm',
    simp,
    rw @nat.mul_div_cancel_left' p m p_dvd_m,
    exact hmp',
  },
  {
    use [m, 0],
    simp,
    cases coprime_or_dvd_of_prime hp m,
    exact h,
    exfalso,
    exact p_dvd_m h,
  },
end

lemma has_coprime_part : ∀ (m p : ℕ), 1 ≤ m → nat.prime p → ∃ (m' i : ℕ), m = (p^i) * m' ∧ p.coprime m' :=
begin
  intros m p,
  exact has_coprime_part_strong m m p (by linarith),
end

lemma prime_pow_eq_one_imp_pow_eq_zero {p i : ℕ} (hp : nat.prime p) : p^i = 1 → i = 0 :=
begin
  induction i with i hi,
  simp,

  by_cases i = 0,
  simp [h],
  intros hh,
  rw hh at hp,
  exact not_prime_one hp,

  have : i.succ = i + 1, exact rfl,
  rw this,
  rw pow_add,
  simp,
  intros hh,
  have : p ∣ 1,
    calc p ∣ p ^ i * p : dvd_mul_left p (p ^ i)
      ... = 1 : hh,
  have : p = 1, exact nat.dvd_one.mp this,
  rw this at hp,
  exact not_prime_one hp,
end

lemma one_lt_prime {p : ℕ} (hp : nat.prime p) : 1 < p :=
begin
  have : 2 ≤ p,
  apply two_le_nat_iff_not_zero_one.mpr,
  split,
  by_contradiction H,
  rw H at hp,
  exact not_prime_zero hp,
  by_contradiction H,
  rw H at hp,
  exact not_prime_one hp,
  linarith,
end

lemma exp_eq_iff_pow_eq {a m n : ℕ} : 2 ≤ a → (m = n ↔ a ^ m = a ^ n) :=
begin
  intros h,
  split,
  exact congr_arg (λ {m : ℕ}, a ^ m),
  intros hh,
  cases nat.lt_trichotomy m n with ht,
  have : a ^ m < a ^ n, exact pow_lt_pow (calc 1 < 2 : by linarith ... ≤ a : h) ht,
  linarith,
  cases h_1 with ht,
  exact ht,
  have : a ^ n < a ^ m, exact pow_lt_pow (calc 1 < 2 : by linarith ... ≤ a : h) h_1,
  linarith,
end

lemma nat_idemp_iff_zero_one {p : ℕ} : p = p * p ↔ p = 0 ∨ p = 1 :=
begin
  have : p = 1 * p, simp,
  conv {
    to_lhs,
    to_lhs,
    rw this,
  },
  split,
  intros h,
  by_cases pp : p = 0,
  left, exact pp,
  have : 0 < p, exact zero_lt_iff.mpr pp,
  rw nat.mul_left_inj this at h,
  right,
  exact h.symm,
  intros h,
  cases h,
  simp [h],
  simp [h],
end

lemma pow_le_abs_pow {a : ℝ} {b : ℕ} : a^b ≤ |a| ^ b :=
begin
  by_cases 0 ≤ a,
  rwa abs_of_nonneg,
  have : a < 0, linarith,
  by_cases even b,
  cases h with k hk,
  rw [hk, pow_mul, pow_mul, ← abs_of_nonneg (pow_two_nonneg a), (pow_abs a)],
  obtain ⟨k, hk⟩ : odd b, simp [h],
  have : a ^ b ≤ 0, {
    rw [hk, pow_add, mul_nonpos_iff],
    left, split,
    rw pow_mul,
    simp [pow_two_nonneg a, pow_nonneg],
    linarith,
  },
  calc a ^ b ≤ 0 : this
    ... ≤ |a| ^ b : by simp [abs_nonneg, pow_nonneg],
end

lemma prime_squarefree {p : ℕ} (hp : nat.prime p) : squarefree p :=
begin
  unfold squarefree,
  intros x hx,
  rw dvd_prime at hx,
  cases hx,
  rw nat.mul_eq_one_iff at hx,
  simp at hx,
  simp [hx],
  have : x ∣ p,
    calc x ∣ x * x : dvd_mul_right x x
      ... = p : hx,
  rw dvd_prime hp at this,
  cases this,
  simp [this],
  rw this at hx,
  have : p = 0 ∨ p = 1, exact nat_idemp_iff_zero_one.mp hx.symm,
  cases this,
  exfalso,
  rw this_1 at hp,
  exact not_prime_zero hp,
  simp [this_1],
  rwa this_1 at this,
  exact hp,
end

lemma Ico_eq_range {n : ℕ} : finset.Ico 0 n = finset.range n :=
begin
  simp,
end

lemma finset.union_singleton {n : ℕ} {s : finset ℕ} : s ∪ {n} = insert n s :=
begin
  ext,
  rw [mem_union, mem_insert, mem_singleton, or_comm],
end

lemma sqrt_one_eq_one : sqrt 1 = 1 := by { symmetry, rw eq_sqrt, simp, linarith, }

lemma one_le_sqrt {n : ℕ} (hn : 1 ≤ n) : 1 ≤ sqrt n :=
begin
  rw sqrt_one_eq_one.symm,
  exact sqrt_le_sqrt hn,
end

lemma nat_sqrt_le_real_sqrt
{a : ℕ} : ↑(sqrt a) ≤ real.sqrt ↑a :=
begin
  rw real.le_sqrt,
  norm_cast,
  exact nat.sqrt_le' a,
  simp, simp,
end

lemma real_sqrt_le_nat_sqrt_succ
{a : ℕ}
:
real.sqrt ↑a ≤ sqrt a + 1
:=
begin
  rw real.sqrt_le_iff,
  split,
  norm_cast,
  simp,
  norm_cast,
  exact le_of_lt (nat.lt_succ_sqrt' a),
end

lemma not_mem_if_gt_max'
{s : finset ℕ}
{hs : s.nonempty}
{n : ℕ}
(hn : max' s hs < n)
:
n ∉ s
:=
begin
  by_contradiction H,
  linarith [calc n ≤ max' s hs : le_max' s n H ... < n : hn],
end

lemma tendsto_abs {f : finset ℕ → ℝ} {a : ℝ} (h : filter.tendsto f at_top (nhds a)) : filter.tendsto (λ n, |f n|) at_top (nhds (|a|)) :=
begin
  rw ← real.norm_eq_abs,
  conv {
    congr,
    funext,
    rw ← real.norm_eq_abs,
  },
  apply filter.tendsto.norm,
  simp [h],
end

lemma finset.subset_finset_min_max {s : finset ℕ} (hs : s.nonempty) : s ⊆ finset.Icc (s.min' hs) (s.max' hs) :=
begin
  rw subset_iff,
  intros x hx,
  simp,
  by_contradiction H,
  push_neg at H,
  by_cases h : s.min' hs ≤ x,
  specialize H h,
  rw finset.max'_lt_iff at H,
  specialize H x hx,
  linarith,
  push_neg at h,
  rw finset.lt_min'_iff at h,
  specialize h x hx,
  linarith,
end

lemma finset.Icc_subset_range {a b : ℕ} : finset.Icc a b ⊆ finset.range (b + 1) :=
begin
  rw subset_iff,
  intros x hx,
  rw finset.mem_range,
  simp at hx,
  simp [lt_succ_of_le hx.right],
end

lemma abs_of_ite
{p : Prop}
{a b : ℝ}
:
|ite p a b| = ite p (|a|) (|b|)
:=
begin
  by_cases h : p,
  simp [h],
  simp [h],
end

lemma ite_const_rw
{n : ℕ}
{f : ℕ → ℝ}
:
∀ (i : ℕ), ite (i = n) (f i) 0 = ite (i = n) (f n) 0
:=
begin
  intros i,
  by_cases i = n,
  simp [h],
  simp [h],
end

lemma interval_eq_Icc {a b : ℝ} (hab : a ≤ b) : [a, b] = set.Icc a b :=
begin
  unfold set.interval,
  have : min a b = a, simp [hab],
  rw this,
  have : max a b = b, simp [hab],
  rw this,
end

lemma interval_eq_Icc' {a b : ℝ} (hab : a ≤ b) : [b, a] = set.Icc a b :=
begin
  unfold set.interval,
  have : min b a = a, simp [hab],
  rw this,
  have : max b a = b, simp [hab],
  rw this,
end

lemma mem_Icc_mem_Ici
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Icc (a : ℝ) ↑b → x ∈ set.Ici (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Icc_mem_Ici'
{a b c : ℕ}
{x : ℝ}
:
x ∈ set.Icc (a : ℝ) ↑b → c ≤ a → x ∈ set.Ici (c : ℝ) :=
begin
  simp,
  intros h _ h',
  calc (c : ℝ) ≤ ↑a : cast_le.mpr h' ... ≤ x : h,
end


lemma mem_Ico_mem_Ici
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ico (a : ℝ) ↑b → x ∈ set.Ici (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ioc_mem_Ioi
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioc (a : ℝ) ↑b → x ∈ set.Ioi (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ioo_mem_Ioi
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ioi (a : ℝ) :=
begin
  simp,
  intros h _,
  exact h,
end

lemma mem_Ico_mem_Icc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ico (a : ℝ) ↑b → x ∈ set.Icc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Icc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Icc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨le_of_lt h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Ioc
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ioc (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨h, le_of_lt h'⟩,
end

lemma mem_Ioo_mem_Ico
{a b : ℕ}
{x : ℝ}
:
x ∈ set.Ioo (a : ℝ) ↑b → x ∈ set.Ico (a : ℝ) ↑b :=
begin
  simp,
  intros h h',
  exact ⟨le_of_lt h, h'⟩,
end

lemma ceil_of_Icc_mem_Icc
{a b : ℕ}
{x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌈x⌉₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  simp,
  split,
  have : ↑a ≤ (⌈x⌉₊ : ℝ), calc ↑a ≤ x : hx.left ... ≤ ↑⌈x⌉₊ : le_ceil x,
  exact cast_le.mp this,
  exact hx.right,
end

lemma floor_of_Icc_mem_Icc
{a b : ℕ} {x : ℝ}
(hx : x ∈ set.Icc (a : ℝ) ↑b)
:
↑⌊x⌋₊ ∈ set.Icc (a : ℝ) ↑b
:=
begin
  simp at hx,
  have : 0 ≤ x, calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : hx.left,
  simp,
  split,
  exact le_floor hx.left,
  have : (⌊x⌋₊ : ℝ) ≤ ↑b, calc ↑⌊x⌋₊ ≤ x : floor_le this ... ≤ ↑b : hx.right,
  exact cast_le.mp this,
end

lemma floor_of_unit_Ioo_val
{k : ℕ} {x : ℝ} : x ∈ set.Ioo (k : ℝ) (↑k + 1) → ⌊x⌋₊ = k :=
begin
  intros hx,
  simp at hx,
  have zero_le_x : 0 ≤ x, {
    have : 0 ≤ k, linarith,
    calc (0 : ℝ) ≤ ↑k : by simp ... ≤ x : by simp [hx.left, le_of_lt],
  },
  have is_le : ⌊x⌋₊ ≤ k, {
    rw ← lt_succ_iff,
    have : (⌊x⌋₊ : ℝ) < k.succ, calc ↑⌊x⌋₊ ≤ x : nat.floor_le zero_le_x ... < k.succ : by simp [hx.right],
    rw cast_lt at this,
    exact this,
  },
  have : ↑k ≤ x, exact le_of_lt hx.left,
  have is_ge : k ≤ ⌊x⌋₊, exact nat.le_floor this,
  linarith [is_le, is_ge],
end

-- How do I use to_floor_semiring?
instance : floor_semiring ℝ :=
{ floor := λ a, ⌊a⌋.to_nat,
  ceil := λ a, ⌈a⌉.to_nat,
  floor_of_neg := λ a ha, int.to_nat_of_nonpos (int.floor_nonpos ha.le),
  gc_floor := λ a n ha, by { rw [int.le_to_nat_iff (int.floor_nonneg.2 ha), int.le_floor], refl },
  gc_ceil := λ a n, by { rw [int.to_nat_le, int.ceil_le], refl } }

lemma floor_off_by_le_one {a b : ℕ} (ha : 0 < a) :
|(b : ℝ) / a - ↑(b / a)| ≤ 1 :=
begin
  by_cases b = 0,
  simp [h],
  have zero_lt_b : 0 < b, exact zero_lt_iff.mpr h,
  by_cases b < a,
  simp [nat.div_eq_zero h],
  rw div_eq_mul_inv,
  have fff: (0 : ℝ) < a, simp [ha],
  have ggg : (0 : ℝ) < a⁻¹, simp [ha],
  have : 0 ≤ (b : ℝ) * (↑a)⁻¹, simp [real.mul_pos, zero_lt_b, ggg],
  rw abs_of_nonneg this,
  rw mul_inv_le_iff fff,
  simp [le_of_lt h],

  rw abs_le,
  let foo := @nat.floor_div_eq_div ℝ (real.linear_ordered_field) (real.floor_semiring) b a,
  rw nat.floor_eq_iff' at foo,
  split,
  linarith [foo.left, foo.right],
  linarith [foo.left, foo.right],
  push_neg at h,
  linarith [nat.div_pos h (by linarith)],
end

end squarefree_sums
