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

lemma two_le_prime {p : ℕ}: nat.prime p → 2 ≤ p :=
begin
  intros hp,
  by_cases p_zero : p = 0,
  exfalso,
  rw p_zero at hp,
  exact not_prime_zero hp,
  by_cases p_one : p = 1,
  exfalso,
  rw p_one at hp,
  exact not_prime_one hp,
  exact two_le_nat_iff_not_zero_one.mpr ⟨ p_zero, p_one ⟩,
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
    have : 2 ≤ p, exact two_le_prime hp,
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

end squarefree_sums
