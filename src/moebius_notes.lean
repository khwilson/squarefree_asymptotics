import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function

/-
The purpose of this file is to prove that μ^2 n = ∑ d^2 ∣ n, μ d. The basic outline
is to show:
  * μ^2 n = ite (squarefree n) 1 0
  * μ^2 is multiplicative
  * n ↦ ∑ d^2 ∣ n, μ d = (sμ * ζ) n where sμ n = ite (is_square n) (μ sqrt n) 0
  * sμ is multiplicative
  * Thus (sμ * ζ) is multiplicative
  * μ^2 and (sμ * ζ) agree on prime powers, and thus
  * μ^2 = (sμ * ζ)

Along the way there are several lemmas we prove, including that μ is multiplicative
(I couldn't find this in mathlib, strangely).

The file has the following outline:
  * General lemmas. These are lemmas that might exist in mathlib, but I couldn't find them
  * Useful functions. Also some lemmas about specific values of those functions
  * Multiplicative functions are equal if they are equal on prime powers.
    - Surely this is somewhere in mathlib, but I couldn't find it!
  * The various useful functions are multiplicative
  * Writing (sμ * ζ) in an inductive fashion
  * Finishing the proof
-/

----------------------------------------
--          GENERAL LEMMAS
----------------------------------------

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

-----------------------------------------
--         SUMMABILITY LEMMAS
-----------------------------------------

lemma one_dirichlet_summable : ∀ (d : ℕ), 2 ≤ d → summable (λ (n : ℕ), ((n : ℝ) ^ d)⁻¹) :=
begin
  intros d hd,
  apply real.summable_nat_pow_inv.mpr,
  linarith,
end

lemma const_dirichlet_summable : ∀ (d : ℕ) (C : ℝ), 2 ≤ d → summable (λ (n : ℕ), C * ((n : ℝ) ^ d)⁻¹) :=
begin
  intros d C hd,
  by_cases C = 0,
  conv { congr, funext, rw h, simp, },
  exact summable_zero,
  rw ← summable_mul_left_iff,
  exact one_dirichlet_summable d hd,
  exact h,
end

lemma bounded_dirichlet_summable
(f : ℕ → ℝ)
(hC : ∃ C, ∀ (n : ℕ), |f n| ≤ C) :
 ∀ (d : ℕ), 2 ≤ d
 → summable (λ (n : ℕ), (f n) * ((n : ℝ) ^ d)⁻¹):=
begin
  intros d hd,
  rw ← summable_abs_iff,
  conv { congr, funext, rw abs_mul},
  cases hC with C hC,
  apply summable_of_nonneg_of_le,
  intros b,
  rw ← abs_mul,
  refine abs_nonneg _,
  intros b,
  have : |f b| * |(↑b ^ d)⁻¹| ≤ C * |(↑b ^ d)⁻¹|, {
    specialize hC b,
    apply mul_le_mul hC rfl.le,
    refine abs_nonneg _,
    transitivity,
    exact abs_nonneg (f b),
    exact hC,
  },
  exact this,
  apply summable.mul_left,
  have : ∀ (b : ℕ), 0 ≤ ((b : ℝ) ^ d)⁻¹, {
    intros b,
    simp,
  },
  conv { congr, funext, rw abs_of_nonneg (this b), },
  exact one_dirichlet_summable d hd,
end

lemma abs_sum_le_sum_abs' {f : ℕ → ℝ} {s : finset ℕ}: | ∑ d in s, f d | ≤ ∑ d in s, | f d | :=
begin
  apply finset.induction_on s,
  simp only [finset.sum_empty, abs_zero],
  {
    intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (abs_add _ _).trans (add_le_add (le_refl (|f i|)) IH),
  },
end

lemma abs_tsum_le_tsum_abs (f : ℕ → ℝ) : | ∑' i, f i | ≤ (∑' i, |f i|) :=
begin
  by_cases summable f,
  have : summable (λ n, |f n|), simp [summable_abs_iff, h],
  sorry,
  have : ¬ summable (λ n, |f n|), simp [summable_abs_iff, h],
  unfold tsum,
  simp [h, this],
end

-----------------------------------------
--         USEFUL FUNCTIONS
-----------------------------------------

def is_square (n : ℕ) : Prop := ∃ s, s * s = n

def ssqrt (n : ℕ) := ite (is_square n) (sqrt n) 0

def sμ' (d : ℕ) := arithmetic_function.moebius (ssqrt d)
def sμ : arithmetic_function ℤ := ⟨
  sμ',
  by {
    unfold sμ',
    unfold ssqrt,
    simp,
  },
⟩

def tμ := sμ * ζ

def squarefree_nat' (d : ℕ) := ite (squarefree d) (1 : ℤ) (0 : ℤ)

def squarefree_nat : arithmetic_function ℤ :=
⟨
  squarefree_nat',
  (by {
    unfold squarefree_nat',
    have : ¬squarefree 0, exact not_squarefree_zero,
    simp [this],
  }),
⟩

-- Decidability
instance : decidable_pred (is_square : ℕ → Prop)
| n := decidable_of_iff' _ (nat.exists_mul_self n)

-- Values
lemma is_square_one : is_square 1 := by { use 1, ring, }

lemma is_square_prime_pow_iff_pow_even : ∀ (p i : ℕ), nat.prime p → (is_square (p ^ i) ↔ even i) :=
begin
  intros p i hp,
  split,
  unfold is_square,
  rintros ⟨s, hs⟩,
  have : s ∣ p ^ i,
    calc s ∣ s * s : dvd_mul_left s s
      ... = p ^ i : hs,
  rw nat.dvd_prime_pow hp at this,
  rcases this with ⟨k, hk, s_eq⟩,
  rw s_eq at hs,
  rw ← pow_add at hs,
  have two_le_p : 2 ≤ p, exact two_le_prime hp,
  rw ← exp_eq_iff_pow_eq two_le_p at hs,
  use k,
  rw ← hs,
  ring,

  rintros ⟨k, hk⟩,
  use p ^ k,
  rw hk,
  rw ← pow_add,
  simp,
  rw ← exp_eq_iff_pow_eq (two_le_prime hp),
  ring,
end

lemma not_is_square_prime {p : ℕ} (hp : nat.prime p) : ¬ is_square p :=
begin
  by_contradiction H,
  have : p = p ^ 1, ring,
  rw this at H,
  have : ¬ even 1, simp,
  exact this ((is_square_prime_pow_iff_pow_even p 1 hp).mp H),
end

lemma sqrt_one_eq_one : 1 = sqrt 1 := by { rw eq_sqrt, simp, linarith, }

lemma ssqrt_one : ssqrt 1 = 1 :=
begin
  unfold ssqrt,
  simp [is_square_one],
  exact sqrt_one_eq_one.symm,
end

lemma ssqrt_prime {p : ℕ} (hp : nat.prime p) : ssqrt p = 0 :=
begin
  unfold ssqrt,
  simp,
  intros p,
  exfalso,
  exact not_is_square_prime hp p,
end

lemma sμ_prime_pow_le_three : ∀ (p i : ℕ), nat.prime p → 3 ≤ i → sμ (p ^ i) = 0 :=
begin
  intros p i hp hi,
  unfold sμ,
  simp,
  unfold sμ',
  unfold ssqrt,
  by_cases even i,
  {
    have : is_square (p ^ i), exact (is_square_prime_pow_iff_pow_even p i hp).mpr h,
    simp [this],
    let fooo := h,
    cases h with k hk,
    rw hk,
    have : p ^ (2 * k) = (p ^ k) * (p ^ k),
    {
      rw mul_comm 2 k,
      rw pow_mul,
      rw pow_two,
    },
    rw this,
    rw sqrt_eq,
    obtain ⟨k', hk'⟩ : ∃ k', k = 2 + k',
    {
      apply two_add,
      by_contradiction H,
      push_neg at H,
      have : i = 3, linarith,
      have : odd i, rw this, use 1, ring,
      exact odd_iff_not_even.mp this fooo,
    },
    rw hk',
    rw pow_add,
    have : ¬ squarefree ((p ^ 2) * (p ^ k')),
    {
      by_contradiction H,
      unfold squarefree at H,
      specialize H p,
      have : p * p ∣ (p^2) * (p ^ k'),
        calc p * p = p ^ 2 : by { rw ← pow_two p, }
          ... ∣ (p ^ 2) * (p ^ k') : dvd_mul_right (p^2) (p^k'),
      specialize H this,
      simp at H,
      rw H at hp,
      exact not_prime_one hp,
    },
    simp [this],
  },
  {
    have : ¬ is_square (p ^ i), {
      by_contradiction H,
      rw (is_square_prime_pow_iff_pow_even p i hp) at H,
      exact h H,
    },
    simp [this],
  },
end

lemma moebius_of_prime {p : ℕ} (hp : nat.prime p) : μ p = -1 :=
begin
  rw arithmetic_function.moebius_apply_of_squarefree (prime_squarefree hp),
  rw arithmetic_function.card_factors_eq_one_iff_prime.mpr hp,
  ring,
end

-- Lemmas
lemma abs_mu_le_one {a : ℕ} : |arithmetic_function.moebius a| ≤ 1 :=
begin
  unfold arithmetic_function.moebius,
  simp,
  by_cases h : squarefree a,
  simp [h],
  simp [h],
end

lemma ssqrt_eq {n : ℕ} : ssqrt (n * n) = n :=
begin
  unfold ssqrt,
  rw sqrt_eq,
  unfold is_square,
  simp,
end

lemma squarefree_eq_μ_μ : squarefree_nat = arithmetic_function.pmul μ μ :=
begin
  ext,
  simp,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  by_cases squarefree x,
  simp [h],
  unfold arithmetic_function.card_factors,
  simp,
  ring_nf,
  rw ← pow_mul,
  rw mul_comm,
  rw pow_mul,
  simp,
  simp [h],
end

lemma prime_not_square {p : ℕ} : nat.prime p → ¬ is_square p :=
begin
  intros hp,
  by_contradiction H,
  cases H with s hs,
  have : s ∣ p,
    calc s ∣ s * s : dvd_mul_left s s
      ... = p : hs,
  rw dvd_prime hp at this,
  cases this,
  rw this at hs,
  simp at hs,
  rw ← hs at hp,
  exact not_prime_one hp,
  rw this at hs,
  have : p = p * p, simp [hs],
  rw nat_idemp_iff_zero_one at this,
  cases this,
  rw this_1 at hp,
  exact not_prime_zero hp,
  rw this_1 at hp,
  exact not_prime_one hp,
end

lemma prod_squares_is_square {a b : ℕ} (ha : is_square a) (hb : is_square b) : is_square (a * b) :=
begin
  cases ha with a' ha',
  cases hb with b' hb',
  use a' * b',
  rw [← ha', ← hb'],
  ring,
end

lemma coprime_prod_not_squares_is_not_square_strong : ∀ (B b a : ℕ), b ≤ B → a.coprime b → ¬ is_square a → ¬ is_square (a * b) :=
begin
  intros B,
  induction B with B hB,
  {
    intros b a hb hab ha_ns,
    have : b = 0, linarith,
    rw this at hab,
    have : a = 1, {
      exact (coprime_zero_right a).mp hab,
    },
    exfalso,
    simp [this] at ha_ns,
    unfold is_square at ha_ns,
    push_neg at ha_ns,
    specialize ha_ns 1,
    simp at ha_ns,
    exact ha_ns,
  },
  {
    intros b a hb hab ha_ns,
    by_cases b_ne_zero : b = 0, {
      exfalso,
      rw b_ne_zero at hab,
      rw coprime_zero_right at hab,
      rw hab at ha_ns,
      exact ha_ns is_square_one,
    },
    by_cases b_ne_one : b = 1, {
      simpa [b_ne_one],
    },
    have two_le_b : 2 ≤ b, exact two_le_nat_iff_not_zero_one.mpr ⟨b_ne_zero, b_ne_one⟩,
    obtain ⟨p, hp, p_dvd_b⟩ : ∃ p, nat.prime p ∧ p ∣ b, exact exists_prime_and_dvd two_le_b,
    obtain ⟨b', i, hb', pb_coprime⟩ := has_coprime_part b p (by linarith) hp,
    by_cases b' = 1,
    sorry,
    have aaa : p^i ≤ B, sorry,
    have bbb : a.coprime (p ^ i), sorry,
    have ccc : ¬ is_square (a * p ^ i), exact hB (p^i) a aaa bbb ha_ns,
    have ddd : (a * p ^ i).coprime b', sorry,
    have eee : b' ≤ B, sorry,
    let foo := hB b' (a * p^i) eee ddd ccc,
    have : a * p ^ i * b' = a * b, rw hb', ring,
    rwa this at foo,
  },
end

lemma coprime_prod_not_squares_is_not_square {a b : ℕ} (hab : a.coprime b) (ha : ¬ is_square a) : ¬ is_square (a * b) :=
begin
  exact coprime_prod_not_squares_is_not_square_strong b b a (by linarith) hab ha,
end

lemma coprime_prod_not_squares_is_not_square' {a b : ℕ} (hab : a.coprime b) (hb : ¬ is_square b) : ¬ is_square (a * b) :=
begin
  conv {
    congr,
    congr,
    rw mul_comm,
  },
  have hab' : b.coprime a, exact (coprime_comm.mp) hab,
  exact coprime_prod_not_squares_is_not_square_strong a a b (by linarith) hab' hb,
end

lemma coprime_ssqrt {a b : ℕ} (ha : is_square a) (hb : is_square b) (hab : a.coprime b) : (ssqrt a).coprime (ssqrt b) :=
begin
  unfold ssqrt,
  simp [ha, hb],
  cases ha with a' ha',
  cases hb with b' hb',
  rw [← ha', ← hb'],
  rw [sqrt_eq, sqrt_eq],
  unfold coprime,
  by_contradiction H,
  have one_lt_gcd : 1 < a'.gcd b', {
    by_cases a = 0,
    {
      rw h at hab,
      simp at hab,
      rw hab at hb',
      rw nat.mul_eq_one_iff at hb',
      rw h at ha',
      rw nat.mul_eq_zero at ha',
      simp at ha',
      simp at hb',
      rw ha' at H,
      rw hb' at H,
      simp at H,
      exfalso,
      exact H,
    },
    have : a' ≠ 0, {
      by_contradiction H,
      rw H at ha',
      simp at ha',
      exact h ha'.symm,
    },
    have : 0 < a'.gcd b', {
      exact gcd_pos_of_pos_left b' (zero_lt_iff.mpr this),
    },
    have : 2 ≤ a'.gcd b', {
      exact two_le_nat_iff_not_zero_one.mpr ⟨zero_lt_iff.mp this, H⟩,
    },
    linarith,
  },
  have gcd_dvd_b : (a'.gcd b') ∣ b,
    calc (a'.gcd b') ∣ b' : @nat.gcd_dvd_right a' b'
      ... ∣ b : dvd.intro b' hb',

  have gcd_dvd_a : (a'.gcd b') ∣ a,
    calc (a'.gcd b') ∣ a' : @nat.gcd_dvd_left a' b'
      ... ∣ a : dvd.intro a' ha',

  have gcd_dvd_gcd : (a'.gcd b') ∣ (a.gcd b), {
    apply @nat.dvd_gcd,
    exact gcd_dvd_a,
    exact gcd_dvd_b,
  },
  have : 0 < (a.gcd b), {
    apply gcd_pos_of_pos_left,
    by_contradiction H,
    simp at H,
    rw H at ha',
    simp at ha',
    rw ha' at one_lt_gcd,
    simp at one_lt_gcd,
    rw H at hab,
    simp at hab,
    rw hab at hb',
    rw nat.mul_eq_one_iff at hb',
    simp at hb',
    linarith,
  },
  have : (a'.gcd b') ≤ (a.gcd b), {
    exact le_of_dvd this gcd_dvd_gcd,
  },
  have : a.gcd b ≠ 1, linarith,
  exact this hab,
end

-- Multiplicativity
lemma is_multiplicative_squarefree {m n : ℕ} (hmn : m.coprime n) : squarefree m ∧ squarefree n ↔ squarefree (m * n) :=
begin
  split,
  rintros ⟨hm, hn⟩,
  rw squarefree_iff_nodup_factors,
  rw list.nodup_iff_count_le_one,
  intros a,
  have hdisjoint : list.disjoint m.factors n.factors, exact coprime_factors_disjoint hmn,
  rw count_factors_mul_of_coprime hmn,
  rw squarefree_iff_nodup_factors at hm,
  rw list.nodup_iff_count_le_one at hm,
  specialize hm a,
  rw squarefree_iff_nodup_factors at hn,
  rw list.nodup_iff_count_le_one at hn,
  specialize hn a,
  by_cases ham : a ∈ m.factors,
  {
    by_cases han : a ∈ n.factors,
    {
      exfalso,
      rw list.disjoint_iff_ne at hdisjoint,
      exact hdisjoint a ham a han rfl,
    },
    {
      have : list.count a n.factors = 0, exact list.count_eq_zero_of_not_mem han,
      simp [this, hm],
    },
  },
  {
    have : list.count a m.factors = 0, exact list.count_eq_zero_of_not_mem ham,
    simp [this, hn],
  },
  by_contradiction H,
  rw H at hn,
  exact not_squarefree_zero hn,
  by_contradiction H,
  rw H at hm,
  exact not_squarefree_zero hm,
  by_contradiction,
  rw mul_eq_zero at h,
  cases h,
  rw h at hm,
  exact not_squarefree_zero hm,
  rw h at hn,
  exact not_squarefree_zero hn,

  ---- Ok, other direction
  intros hmn_sq,
  split,

  by_contradiction H,
  unfold squarefree at H,
  push_neg at H,
  rcases H with ⟨x, hx, hxx⟩,
  unfold squarefree at hmn_sq,
  specialize hmn_sq x,
  have : x * x ∣ m * n,
    calc x * x ∣ m : hx
      ... ∣ m * n : dvd_mul_right m n,
  exact hxx (hmn_sq this),

  by_contradiction H,
  unfold squarefree at H,
  push_neg at H,
  rcases H with ⟨x, hx, hxx⟩,
  unfold squarefree at hmn_sq,
  specialize hmn_sq x,
  have : x * x ∣ m * n,
    calc x * x ∣ n : hx
      ... ∣ m * n : dvd_mul_left n m,
  exact hxx (hmn_sq this),
end

lemma is_multiplicative_ssqrt {a b : ℕ} (hab : a.coprime b) : ssqrt (a * b) = (ssqrt a) * (ssqrt b) :=
begin
  by_cases ha : is_square a,
  {
    by_cases hb : is_square b,
    {
      have : is_square (a * b), exact prod_squares_is_square ha hb,
      unfold ssqrt,
      simp [ha, hb, this],
      cases ha with a' ha',
      cases hb with b' hb',
      rw [← ha', ← hb'],
      rw [sqrt_eq, sqrt_eq],
      have : a' * a' * (b' * b') = (a' * b') * (a' * b'), ring,
      rw this,
      rw sqrt_eq,
    },
    {
      have : ¬ is_square (a * b), exact coprime_prod_not_squares_is_not_square' hab hb,
      unfold ssqrt,
      simp [ha, hb, this],
    },
  },
  {
    have : ¬ is_square (a * b), exact coprime_prod_not_squares_is_not_square hab ha,
    unfold ssqrt,
    simp [ha, this],
  },
end

lemma is_multiplicative_moebius : arithmetic_function.is_multiplicative arithmetic_function.moebius :=
begin
  unfold arithmetic_function.is_multiplicative,
  split,
  simp,
  intros m n hmn,
  by_cases hm_sq : squarefree m,
  {
    by_cases hn_sq : squarefree n,
    {
      have hmn_sq : squarefree (m * n),
      exact (is_multiplicative_squarefree hmn).mp ⟨hm_sq, hn_sq⟩,
      simp [hm_sq, hn_sq, hmn_sq],
      rw arithmetic_function.card_factors_mul,
      rw pow_add,
      by_contradiction H,
      rw H at hm_sq,
      exact not_squarefree_zero hm_sq,
      by_contradiction H,
      rw H at hn_sq,
      exact not_squarefree_zero hn_sq,
    },
    {
      have : ¬ squarefree (m * n), {
        by_contradiction H,
        exact hn_sq ((is_multiplicative_squarefree hmn).mpr H).right,
      },
      simp [this, hn_sq],
    },
  },
  have : ¬ squarefree (m * n), {
    by_contradiction H,
    exact hm_sq ((is_multiplicative_squarefree hmn).mpr H).left,
  },
  simp [this, hm_sq],
end

lemma is_multiplicative_sμ : arithmetic_function.is_multiplicative sμ :=
begin
  unfold arithmetic_function.is_multiplicative,
  split,
  {
    unfold sμ,
    simp,
    unfold sμ',
    unfold ssqrt,
    have : is_square 1, {
      use 1,
      ring,
    },
    simp [this],
    have : sqrt 1 = 1, {
      have : 1 = 1 * 1, ring,
      conv {
        to_lhs,
        congr,
        rw this,
      },
      apply sqrt_eq,
    },
    simp [this],
  },
  {
    intros m n hmn,
    unfold sμ,
    simp,
    unfold sμ',
    have : ssqrt (m * n) = (ssqrt m) * (ssqrt n), exact is_multiplicative_ssqrt hmn,
    rw this,
    by_cases hm : is_square m,
    {
      by_cases hn : is_square n,
      {
        have : (ssqrt m).coprime (ssqrt n), exact coprime_ssqrt hm hn hmn,
        simp [is_multiplicative_moebius, this],
      },
      {
        unfold ssqrt,
        have : ¬ is_square (m * n), exact coprime_prod_not_squares_is_not_square' hmn hn,
        simp [hm, hn, this],
      },
    },
    {
      unfold ssqrt,
      have : ¬ is_square (m * n), exact coprime_prod_not_squares_is_not_square hmn hm,
      simp [hm, hn, this],
    },
  },
end

lemma is_multiplicative_tμ : arithmetic_function.is_multiplicative tμ :=
begin
  unfold tμ,
  apply is_multiplicative_sμ.mul,
  simp [arithmetic_function.is_multiplicative_zeta, arithmetic_function.is_multiplicative.nat_cast],
end

lemma is_multiplicative_squarefree_nat : arithmetic_function.is_multiplicative squarefree_nat :=
begin
  unfold arithmetic_function.is_multiplicative,
  split,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  simp [squarefree_one],
  intros m n,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  intros h,
  by_cases hm : squarefree m,
  {
    by_cases hn : squarefree n,
    {
      have : squarefree (m * n), exact (is_multiplicative_squarefree h).mp ⟨hm, hn⟩,
      simp [this, hm, hn],
    },
    {
      have : ¬squarefree (m * n), {
        by_contradiction H,
        exact hn ((is_multiplicative_squarefree h).mpr H).right,
      },
      simp [this, hm, hn],
    },
  },
  {
    have : ¬squarefree (m * n), {
      by_contradiction H,
      exact hm ((is_multiplicative_squarefree h).mpr H).left,
    },
    simp [this, hm],
  },
end

----------------------------------------------------------------------------
--         MULTIPLICATIVE FUNCTIONS DEFINED BY VALUES ON PRIME POWERS
----------------------------------------------------------------------------

-- nat.multiplicative_factorization'
lemma multiplicative_eq_iff_eq_on_prime_powers {f g : arithmetic_function ℤ}
(hf : arithmetic_function.is_multiplicative f)
(hg : arithmetic_function.is_multiplicative g)
:
f = g ↔ ∀ (p i : ℕ), nat.prime p → f (p^i) = g (p^i)
:=
begin
  split,
  intros h p i _,
  simp [h],
  intros h,
  ext m,
  apply nat.strong_induction_on m,
  clear m,
  intros m,
  intros h_ind,

  by_cases m_ne_zero : m = 0,
  simp [m_ne_zero],
  by_cases m_ne_one : m = 1,
  simp [m_ne_one, hf, hg],
  have one_le_m : 1 ≤ m, linarith [zero_lt_iff.mpr m_ne_zero],
  have zero_lt_m : 0 < m, linarith,
  have two_le_m : 2 ≤ m, exact two_le_nat_iff_not_zero_one.mpr ⟨m_ne_zero, m_ne_one⟩,
  obtain ⟨p, p_is_prime, p_dvd_m⟩ : ∃ (p : ℕ), nat.prime p ∧ p ∣ m, exact exists_prime_and_dvd two_le_m,
  have : ∃ (m' i : ℕ), m = (p^i) * m' ∧ p.coprime m', exact has_coprime_part m p one_le_m p_is_prime,
  rcases this with ⟨m', i, m_eq, p_coprime⟩,
  have pi_coprime_m' : (p^i).coprime m', {
    by_cases i = 0,
    simp [h],
    have : 0 < i, exact zero_lt_iff.mpr h,
    exact (coprime_pow_left_iff this p m').mpr p_coprime,
  },
  rw m_eq,
  have hfs : f(p ^ i * m') = f(p^i) * f(m'), simp [hf, arithmetic_function.is_multiplicative, pi_coprime_m'],
  have hgs : g(p ^ i * m') = g(p^i) * g(m'), simp [hg, arithmetic_function.is_multiplicative, pi_coprime_m'],
  rw [hfs, hgs],
  have m'_lt_m : m' < m,
  {
    have aaa : m' ≠ m,
    {
      by_contradiction H,
      rw H at p_coprime,
      unfold coprime at p_coprime,
      have : p ∣ p.gcd m,
      {
        rw nat.dvd_gcd_iff,
        split,
        exact dvd_rfl,
        exact p_dvd_m,
      },
      have : p ≤ p.gcd m, exact le_of_dvd (by linarith [p_coprime]) this,
      have : 1 < p, exact one_lt_prime p_is_prime,
      linarith,
    },
    have : m' ∣ m,
      calc m' ∣ p ^ i * m' : dvd_mul_left m' (p ^ i)
        ... = m : m_eq.symm,
    have bbb : m' ≤ m, exact nat.le_of_dvd zero_lt_m this,
    exact (ne.le_iff_lt aaa).mp bbb,
  },
  rw h p i p_is_prime,
  rw h_ind m' m'_lt_m,
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

lemma tμ_1 : tμ 1 = 1 := by simp [is_multiplicative_tμ]

lemma tμ_ind {p i : ℕ} (hp : nat.prime p) :
tμ (p ^ (i + 1)) = tμ (p ^ i) + sμ (p ^ (i + 1)) :=
begin
  unfold tμ,
  unfold sμ,
  simp,
  unfold sμ',

  rw nat.divisors_prime_pow hp (i + 1),
  rw ← Ico_eq_range,
  have munion : finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1 + 1)) =
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1))) ∪
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico (i + 1) (i + 1 + 1))), {
    have : (finset.Ico 0 (i + 1 + 1)) = (finset.Ico 0 (i + 1)) ∪ (finset.Ico (i + 1) (i + 1 + 1)), {
      simp,
      rw range_succ,
      rw finset.union_singleton,
    },
    rw this,
    rw map_union,
  },
  have udisjoint : disjoint
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico 0 (i + 1)))
  (finset.map {to_fun := pow p, inj' := _} (finset.Ico (i + 1) (i + 1 + 1))), {
    rw disjoint_iff_ne,
    intros a ha b hb,
    rw finset.mem_map at ha,
    rcases ha with ⟨ia, hia, via⟩,
    rw finset.mem_map at hb,
    rcases hb with ⟨ib, hib, vib⟩,
    simp at via,
    simp at vib,
    by_contradiction H,
    rw ← H at vib,
    rw ← vib at via,
    rw ← exp_eq_iff_pow_eq (two_le_prime hp) at via,
    simp at hia,
    simp at hib,
    linarith [vib, hia, hib, via],
  },
  rw munion,
  rw finset.sum_union udisjoint,
  simp,
  rw nat.divisors_prime_pow hp i,
  simp,
end

lemma barrr {i p : ℕ} (hp : nat.prime p) : 2 ≤ i → squarefree_nat (p^i) = 0 :=
begin
  intros hi,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  simp,
  by_contradiction H,
  have : p * p ∣ p ^ i, {
    obtain ⟨i', hi'⟩ : ∃ i', i = 2 + i', exact two_add hi,
    rw hi',
    rw pow_add,
    rw pow_two,
    exact dvd_mul_right (p * p) (p ^ i'),
  },
  unfold squarefree at H,
  specialize H p this,
  simp at H,
  rw H at hp,
  exact not_prime_one hp,
end

--------------------------------------------------------------------------
--         THEOREM 1: SQUAREFREE CAN BE WRITTEN AS SUM OF MU
--------------------------------------------------------------------------
lemma case_0 (p : ℕ) (hp : nat.prime p) : squarefree_nat p = tμ 1 + sμ p :=
begin
  unfold squarefree_nat,
  unfold sμ,
  simp,
  unfold squarefree_nat',
  unfold sμ',
  simp [prime_squarefree hp, is_multiplicative_tμ, ssqrt_prime hp],
end

lemma case_1 (p : ℕ) (hp : nat.prime p) (hi : squarefree_nat p = tμ p) : squarefree_nat (p ^ 2) = tμ p + sμ (p ^ 2) :=
begin
  rw barrr hp (calc 2 ≤ 2 : by linarith),
  rw ← hi,
  unfold sμ,
  unfold squarefree_nat,
  simp,
  unfold squarefree_nat',
  unfold sμ',
  simp [prime_squarefree hp],
  rw pow_two p,
  rw ssqrt_eq,
  rw moebius_of_prime hp,
  ring,
end

theorem squarefree_nat_eq_tμ : squarefree_nat = tμ :=
begin
  rw multiplicative_eq_iff_eq_on_prime_powers is_multiplicative_squarefree_nat is_multiplicative_tμ,
  intros p i hp,
  induction i with i hi,
  simp [is_multiplicative_tμ, is_multiplicative_squarefree_nat],
  rw tμ_ind hp,

  by_cases c1 : i = 0,
  simp [c1, case_0 p hp],

  by_cases c2 : i = 1,
  simp [c2] at hi,
  simp [c2, case_1 p hp hi],

  have : 2 ≤ i, exact two_le_nat_iff_not_zero_one.mpr ⟨c1, c2⟩,
  rw ← hi,
  simp [barrr hp this, barrr hp (le_of_lt (calc 2 ≤ i : this ... < i.succ : lt_succ_self i))],
  simp [foo p (i + 1) hp (by linarith)],
end


--------------------------------------------------------------------
--       REWRITE tμ IN A WAY MORE CONDUCIVE TO SUM MANIPULATION
--------------------------------------------------------------------

lemma blah {n : ℕ} : μ (ssqrt n) = ite (is_square n) (μ (sqrt n)) 0 :=
begin
  unfold ssqrt,
  by_cases is_square n,
  simp [h],
  simp [h],
end

lemma one_le_sqrt {n : ℕ} (hn : 1 ≤ n) : 1 ≤ sqrt n :=
begin
  rw sqrt_one_eq_one,
  exact sqrt_le_sqrt hn,
end

lemma ifififif {n : ℕ} : set.bij_on (λ i, sqrt i) (finset.filter is_square n.divisors) (finset.filter (λ x, x ^ 2 ∣ n) (finset.Icc 1 n)) :=
begin
  unfold set.bij_on,
  unfold set.maps_to,
  split,
  intros x hx,
  simp at hx,
  simp,
  split,
  split,
  have : x ≠ 0, {
    by_contradiction H,
    rw H at hx,
    exact hx.left.right (zero_dvd_iff.mp hx.left.left),
  },
  exact one_le_sqrt (one_le_iff_ne_zero.mpr this),
  have : x ≤ n, exact le_of_dvd (zero_lt_iff.mpr hx.left.right) hx.left.left,
  calc sqrt x ≤ sqrt n : sqrt_le_sqrt this
    ... ≤ n : sqrt_le_self n,
  rcases hx.right with ⟨x', hx'⟩,
  rw ← hx',
  rw sqrt_eq,
  rw pow_two,
  rw hx',
  exact hx.left.left,
  split,
  unfold set.inj_on,
  intros x hx y hy hf,
  simp at hx,
  simp at hy,
  rcases hx.right with ⟨x', hx'⟩,
  rcases hy.right with ⟨y', hy'⟩,
  rw [← hx', ← hy', sqrt_eq, sqrt_eq] at hf,
  calc x = x' * x' : hx'.symm
    ... = y' * y' : by rw hf
    ... = y : hy',
  unfold set.surj_on,
  -- Why so many unfolds? Why doesn't rw subset_iff work?
  unfold has_subset.subset,
  unfold set.subset,
  intros a ha,
  simp at ha,
  simp,
  use a^2,
  split,
  split,
  split,
  exact ha.right,
  linarith,
  use a,
  rw pow_two,
  rw [pow_two, sqrt_eq],
end

/- This repackackges finset.sum_bij as specifying the _forward_ function -/
lemma finset.sum_bij''
(f : ℕ → ℤ) (g : ℕ → ℕ) (s t : finset ℕ) (hg : set.bij_on g t s) :
∑ i in t, f (g i) = ∑ i in s, f i :=
begin
  rcases hg with ⟨hg1, hg2, hg3⟩,
  apply finset.sum_bij,

  have : ∀ (a : ℕ) (ha : a ∈ t), (λ (b : ℕ) (H : b ∈ t), g b) a ha ∈ s, {
    intros a ha,
    simp,
    unfold set.maps_to at hg1,
    exact hg1 ha,
  },
  exact this,
  intros a ha,
  congr,
  intros a b ha hb hginv,
  unfold set.inj_on at hg2,
  simp at hginv,
  exact hg2 ha hb hginv,
  intros b hb,
  unfold set.surj_on at hg3,
  simp,
  unfold set.image at hg3,
  simp at hg3,
  unfold has_subset.subset at hg3,
  unfold set.subset at hg3,
  specialize hg3 hb,
  simp at hg3,
  rcases hg3 with ⟨a', ha', ha''⟩,
  use a',
  exact ⟨ha', ha''.symm⟩,
end

lemma rw_tμ {n : ℕ}: tμ n = ∑ d in finset.Icc 1 n, ite (d ^ 2 ∣ n) (μ d) 0 :=
begin
  unfold tμ,
  simp,
  unfold sμ,
  simp,
  unfold sμ',
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw blah,
  },
  rw [sum_ite, sum_ite],
  simp,
  apply finset.sum_bij'',
  exact ifififif,
end

---------------------------------------------------------------------------------
--       DEALING WITH O MANIPULATION (MIGHT BE IN ASYMPTOTICS PACKAGE ALREADY)
---------------------------------------------------------------------------------

/- Convenience notation for f = g + O(h) -/
-- {E : Type*} [has_norm E] {F : Type*} [has_norm F]
def is_Ot {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (l : filter α) : Prop :=
∃ c : ℝ, asymptotics.is_O_with c (f - g) h l

--
theorem is_Ot_transitive {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (k : α → ℝ) (l : filter α) :
is_Ot f g h l → is_Ot g k h l → is_Ot f k h l :=
begin
  sorry,
end


--------------------------------------------
--           THEOREM 2: THE BIG BAD
--------------------------------------------

def num_divides_upto (d : ℕ) (n : ℕ) := ((finset.Icc 1 n).filter (has_dvd.dvd d)).card

-- Swap the order of summation (the really key point)
lemma step1 :
∀ (x : ℕ),
(∑ n in finset.Icc 1 x, ∑ d in finset.Icc 1 x, ite (d ^ 2 ∣ n) (μ d) 0) =
(∑ d in finset.Icc 1 x, ((μ d) * ((finset.Icc 1 x).filter (has_dvd.dvd (d ^ 2))).card))
:=
begin
  intros x,
  have : ∀ (y : ℕ) (s : finset ℕ), ↑(∑ a in s, 1) * (μ y) = ∑ a in s, (μ y), {
    simp,
  },
  conv {
    to_rhs,
    congr,
    skip,
    funext,
    rw card_eq_sum_ones,
    rw mul_comm,
    rw this,
  },
  rw finset.sum_comm,
  congr,
  funext,
  rw sum_ite,
  simp,
end

-- Rewrite inner sum term as floor ( x / d^2 )
lemma Icc_neighbor {a b c : ℕ} (hab : a ≤ b) (hbc : b + 1 ≤ c) :
  finset.Icc a c = finset.Icc a b ∪ finset.Icc (b + 1) c ∧
  disjoint (finset.Icc a b) (finset.Icc (b + 1) c) :=
begin
  split,
  ext x,
  split,
  simp,
  intros hax hxc,
  simp [hax, hxc],
  by_contradiction H,
  push_neg at H,
  linarith [H],
  simp,
  intros h,
  cases h,
  simp [h.left, h.right],
  linarith,
  simp [h.left, h.right],
  linarith,
  rw disjoint_iff_ne,
  simp,
  intros x hax hxb y hby hyc,
  by_contradiction H,
  rw ← H at hby,
  linarith,
end

lemma num_divides_upto_eq (d n : ℕ) : ((finset.Icc 1 n).filter (has_dvd.dvd d)).card = n.div d :=
begin
  induction n with n hn,
  dec_trivial,
  by_cases hh : n = 0,
  simp [hh],
  by_cases hd : d = 0,
  simp [hd],
  dec_trivial,
  by_cases hd' : d = 1,
  simp [hd'],
  dec_trivial,
  have : 2 ≤ d, exact two_le_nat_iff_not_zero_one.mpr ⟨hd, hd'⟩,
  have : (1 : ℕ).div d = (1 : ℕ) / d, exact rfl,
  rw this,
  have : (1 : ℕ) / d = 0, exact nat.div_eq_zero (by linarith [this]),
  rw this,
  rw card_eq_zero,
  rw eq_empty_iff_forall_not_mem,
  intros x,
  by_contradiction H,
  rw mem_filter at H,
  simp at H,
  rcases H with ⟨aa, bb⟩,
  rw aa at bb,
  have : d = 1, exact nat.dvd_one.mp bb,
  exact hd' this,

  have aaa : 1 ≤ n, exact one_le_iff_ne_zero.mpr hh,
  have bbb : n + 1 ≤ n + 1, linarith,
  have ccc : n.succ = n + 1, exact rfl,

  obtain ⟨is_union, is_disjoint⟩ := Icc_neighbor aaa bbb,
  rw ccc,
  rw is_union,
  rw filter_union,
  rw card_disjoint_union (disjoint_filter_filter is_disjoint),
  rw hn,
  simp,
  have dvd_case : d ∣ n.succ → (finset.filter (has_dvd.dvd d) {n.succ}).card = 1, {
    intros hd,
    rw card_eq_one,
    use n.succ,
    rw finset.eq_singleton_iff_unique_mem,
    split,
    rw finset.mem_filter,
    simp [hd],
    intros x,
    rw finset.mem_filter,
    rintros ⟨hx, hxx⟩,
    exact finset.mem_singleton.mp hx,
  },
  have not_dvd_case : ¬ (d ∣ n.succ) → (finset.filter (has_dvd.dvd d) {n.succ}).card = 0, {
    intros hd,
    rw card_eq_zero,
    rw finset.eq_empty_iff_forall_not_mem,
    intros x,
    rw finset.mem_filter,
    push_neg,
    intros hx,
    rw finset.mem_singleton at hx,
    rwa ← hx at hd,
  },
  by_cases d ∣ n.succ,
  {
    rw dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
  {
    rw not_dvd_case h,
    have : n.succ.div d = (n + 1) / d, exact rfl,
    rw this,
    rw succ_div,
    have : n.div d = n / d, exact rfl,
    rw this,
    have : n.succ = n + 1, exact rfl,
    rw this at h,
    simp [h],
  },
end

lemma step2 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * ((finset.Icc 1 x).filter (has_dvd.dvd (d ^ 2))).card)) =
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  apply finset.sum_congr,
  simp,
  intros y hy,
  rw num_divides_upto_eq,
end

-- Shorten the sum
lemma sqrt_magnitude {n : ℕ} : 2 ≤ n → 1 ≤ sqrt n ∧ (sqrt n + 1) ≤ n :=
begin
  intros hn,
  split,
  linarith [sqrt_pos.mpr (calc 0 < 2 : by linarith ... ≤ n : hn)],
  linarith [sqrt_lt_self (calc 1 < 2 : by linarith ... ≤ n : hn)],
end

lemma step3 :
∀ (x : ℕ),
(∑ d in finset.Icc 1 x, ((μ d) * x.div (d^2))) =
(∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2)))
:=
begin
  intros x,
  by_cases x0 : x = 0,
  rw x0,
  simp,
  by_cases x1 : x = 1,
  rw x1,
  rw ← sqrt_one_eq_one,
  have x2 : 2 ≤ x, exact two_le_nat_iff_not_zero_one.mpr ⟨x0, x1⟩,
  have : 1 ≤ sqrt x ∧ (sqrt x + 1) ≤ x, exact sqrt_magnitude x2,
  obtain ⟨fs_union, fs_disjoint⟩ := Icc_neighbor this.left this.right,
  rw fs_union,
  rw finset.sum_union fs_disjoint,
  simp,
  apply sum_eq_zero,
  intros y hy,
  have : x.div (y ^ 2) = x / (y ^ 2), exact rfl,
  rw this,
  simp,
  right,
  rw int.div_eq_zero_of_lt,
  linarith,
  simp at hy,
  have aaa : x < ((sqrt x) + 1) ^ 2, exact nat.lt_succ_sqrt' x,
  zify at aaa,
  rcases hy with ⟨hyl, hyr⟩,
  have hyl2 : ((sqrt x) + 1) ^ 2 ≤ y ^ 2, exact nat.pow_le_pow_of_le_left hyl 2,
  zify at hyl2,
  calc ↑x < (↑(sqrt x) + 1) ^ 2 : aaa
    ... ≤ ↑y ^ 2 : hyl2,
end


-- It's a lot easier to work with Ico's than Icc's because programming
-- But this means we pick up an O(1) term. Prove this is true!
lemma Icc_eq_Ico_union_singleton {a b : ℕ} (hab : a ≤ b) :
finset.Icc a b = finset.Ico a b ∪ {b} ∧ disjoint (finset.Ico a b) {b} :=
begin
  simp,
  ext x,
  simp,
  split,
  rintros ⟨hax, hxb⟩,
  simp [hax, hxb, lt_or_eq_of_le],
  intros h,
  cases h,
  simp [h, le_of_lt],
  simp [hab, h, le_of_eq],
end

lemma quadratic_monotone_eventually
{a b c : ℝ}
(ha : 0 < a)
:
monotone_on (λ x, a * x ^ 2 + b * x + c) (set.Ici (-b / (2 * a)))
:=
begin
  -- This computation is annoyingly difficult
  have two_a_ne_zero : 2 * a ≠ 0, linarith [ha],
  have : 0 = a * 2 * (-b / (2 * a)) + b,
    ring_nf,
    have : (2 * (2 * a)⁻¹ * b * a) = ((2 * a) * (2 * a)⁻¹ * b), ring,
    rw this,
    rw mul_inv_cancel two_a_ne_zero,
    ring,

  have final_ineq : ∀ (x : ℝ), -b / (2 * a) ≤ x → 0 ≤ a * 2 * x + b,
    intros x hx,
    rw this,
    -- Why does add_lt_add_of_lt_of_le not have an equivalent with all lt's replaced by le's?
    apply add_le_add,
    rw mul_le_mul_left,
    exact hx,
    linarith [ha],
    exact rfl.le,

  let f := (polynomial.monomial 2 a) + (polynomial.monomial 1 b) + (polynomial.C c),
  have : (λ x, f.eval x) = (λ (x : ℝ), a * x ^ 2 + b * x + c),
  {
    funext,
    simp,
  },
  rw ← this,
  apply convex.monotone_on_of_deriv_nonneg (convex_Ici (-b / (2 * a))) (polynomial.continuous_on f) (polynomial.differentiable_on f),
  intros x hx,
  have aa : f.derivative = polynomial.monomial 1 (a * 2) + polynomial.C b, {
    simp,
  },
  have bb : deriv (λ (x : ℝ), f.eval x) = (λ (x : ℝ), (f.derivative.eval x)), {
    funext,
    simp,
    ring,
  },
  rw [bb, aa],
  simp,
  simp at hx,
  exact final_ineq x (le_of_lt hx),
end

lemma nat_div_sqrt_sqrt_eq_one
{n : ℕ}
:
9 ≤ n → n.div (sqrt n * sqrt n) = 1
:=
begin
  -- In fact, this value for n = 8 is 3 which is the max
  intros hn,
  have one_le_sqrt_n : 1 ≤ sqrt n,  {
    rw sqrt_one_eq_one,
    apply sqrt_le_sqrt,
    calc 1 ≤ 9 : by linarith ... ≤ n : hn,
  },

  have zero_lt_sqrt_n : 0 < sqrt n, calc 0 < 1 : by linarith ... ≤ sqrt n : one_le_sqrt_n,
  have le_half : n / (sqrt n * sqrt n) ≠ 0, {
    by_contradiction H,
    rw nat.div_eq_zero_iff at H,
    let bar := calc sqrt n * sqrt n ≤ n : nat.sqrt_le n ... < sqrt n * sqrt n : H,
    linarith,
    simp [zero_lt_sqrt_n],
  },

  have : n ≤ (sqrt n + 1) * (sqrt n + 1), exact le_of_lt (nat.lt_succ_sqrt n),
  have blah : n / (sqrt n * sqrt n) ≤ ((sqrt n + 1) * (sqrt n + 1)) / ((sqrt n) * (sqrt n)), {
    exact nat.div_le_div_right this,
  },
  have : ((sqrt n + 1) * (sqrt n + 1)) = (sqrt n * sqrt n) + 2 * sqrt n + 1, ring,
  rw this at blah,
  have zzz : 2 * sqrt n + 1 < sqrt n * sqrt n,
  {
    let f := (λ (x : ℝ), 1 * x ^ 2 + -2 * x + -1),
    have : monotone_on f (set.Ici (- - 2 / (2 * 1))),
      exact quadratic_monotone_eventually (by simp),

    have aa : 3 ≤ sqrt n, {
      have : 9 = 3 * 3, dec_trivial,
      have : sqrt 9 = 3, rw this, exact sqrt_eq 3,
      calc 3 = sqrt 9 : this.symm ... ≤ sqrt n : sqrt_le_sqrt hn,
    },
    have aa' : (3 : ℝ) ≤ ↑(sqrt n), {
      have : (3 : ℝ) = ↑(3 : ℕ), simp,
      rw this,
      exact cast_le.mpr aa,
    },
    have bb : - - (2: ℝ) / (2 * 1) ≤ 3, simp,
    have bb' : (3 : ℝ) ∈ set.Ici (- - (2: ℝ) / (2 * 1)), simp [bb],
    have cc : - - (2 : ℝ) / (2 * 1) ≤ ↑(sqrt n), calc - - (2 : ℝ) / (2 * 1) ≤ (3 : ℝ) : bb ... ≤ ↑(sqrt n) : aa',
    have cc' : ↑(sqrt n) ∈ set.Ici (- - (2: ℝ) / (2 * 1)), simp, linarith,
    unfold monotone_on at this,
    specialize this bb' cc' aa',
    have aa : 0 < f 3, simp,
    linarith,
    have bb : f ↑(sqrt n) = ↑((sqrt n * sqrt n) - 2 * (sqrt n) - 1), sorry, -- So much casting nonsense
    have : (0 : ℝ) < ↑((sqrt n * sqrt n) - 2 * (sqrt n) - 1), linarith,
    have : 0 < (sqrt n * sqrt n) - 2 * (sqrt n) - 1, {
      exact cast_lt.mp this,
    },
    sorry,  -- Why is it so damn hard to move things around inequalities even _after_ casts?
  },
  have : (2 * sqrt n + 1) / (sqrt n * sqrt n) = 0, exact nat.div_eq_zero zzz,
  have : (sqrt n * sqrt n + 2 * sqrt n + 1) / (sqrt n * sqrt n) = (2 * sqrt n + 1) / (sqrt n * sqrt n) + 1,
    apply nat.add_div_left (2 * sqrt n + 1),
    linarith,
  rw nat.div_eq_zero zzz at this,
  rw this at blah,
  simp at blah,

  -- OK, I have that it's ≤ 1 and that it ≠ 0 so why is this so hard :'-(
    sorry,
end

lemma step35 :
is_Ot
(λ x, (∑ d in finset.Icc 1 (sqrt x), ((μ d) * x.div (d^2))))
(λ x, (∑ d in finset.Ico 1 (sqrt x), ((μ d) * x.div (d^2))))
1
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros n hn,
  rw real.norm_eq_abs,
  have : 1 ≤ sqrt n, {rw sqrt_one_eq_one, apply sqrt_le_sqrt, calc 1 ≤ 100 : by linarith ... ≤ n : hn, },
  rw (Icc_eq_Ico_union_singleton this).left,
  rw finset.sum_union (Icc_eq_Ico_union_singleton this).right,
  simp,
  rw pow_two,
  have : 9 ≤ n, linarith,
  rw nat_div_sqrt_sqrt_eq_one this,
  simp,
  -- Explicit casts :-(
  conv {
    to_lhs,
    rw ← int.cast_abs,
  },
  rw ← int.cast_one,
  rw int.cast_le,
  exact abs_mu_le_one,
end


-- Converting from natural division to real division only picks up √x in error
def sum_μ_times_floor_n_over_d2 (n : ℕ) :=
((∑ d in finset.Ico 1 (sqrt n), (μ d) * n.div (d^2)) : ℝ)

def sum_μ_times_n_over_d2 (n : ℕ) :=
∑ d in finset.Ico 1 (sqrt n), ↑(μ d) * ↑n * ((d : ℝ) ^ 2)⁻¹

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

lemma dumbdumb {a b c d : ℝ} : |a * b - a * c * d| = |a| * |b - c * d| := by sorry

lemma afaf {a b : ℝ} : |a| ≤ 1 ∧ |b| ≤ 1 → |a| * |b| ≤ 1 :=
begin
  sorry,
end

lemma step4 :
is_Ot
sum_μ_times_floor_n_over_d2
sum_μ_times_n_over_d2
(λ n, ((sqrt n) : ℝ))
at_top
:=
begin
  unfold is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  rw real.norm_eq_abs,
  unfold sum_μ_times_floor_n_over_d2,
  unfold sum_μ_times_n_over_d2,
  rw ← finset.sum_sub_distrib,
  transitivity,
  exact abs_sum_le_sum_abs',
  have u1 : ∀ (d : ℕ), b.div (d ^ 2) = b / (d ^ 2), {
    intros d,
    unfold has_div.div,
  },
  have u2 : ∀ (d : ℕ), (b : ℝ) * (↑d ^ 2)⁻¹ = (b : ℝ) / ↑(d ^ 2), {
    intros d,
    rw div_eq_mul_inv,
    simp,
  },
  conv {to_lhs, congr, skip, funext, rw dumbdumb, rw u1 d, rw u2 d, rw abs_sub_comm,},
  have u3 : ∀ (d : ℕ), 0 < d → |((μ d) : ℝ)| * |(b : ℝ) / ↑(d ^ 2) - ↑(b / d ^ 2)| ≤ 1,
  {
    intros d hd,
    apply afaf,
    split,
    rw ← int.cast_abs,
    have : (1 : ℝ) = ↑(1 : ℤ), simp,
    rw this,
    rw int.cast_le,
    exact abs_mu_le_one,
    have : 0 < d ^ 2, { rw pow_two, exact (zero_lt_mul_left hd).mpr hd,},
    exact floor_off_by_le_one this,
  },
  have u4 : ∑ (d : ℕ) in finset.Ico 1 (sqrt b), |((μ d) : ℝ)| * |(b : ℝ) / ↑(d ^ 2) - ↑(b / d ^ 2)| ≤ ∑ (d : ℕ) in finset.Ico 1 (sqrt b), 1,
  {
    apply finset.sum_le_sum,
    intros i hi,
    simp at hi,
    exact u3 i (by linarith [hi.left]),
  },
  transitivity,
  exact u4,
  simp,
end

def μ_over_d2 (d : ℕ) := ↑(μ d) * ((d : ℝ) ^ 2)⁻¹

def μ_sum_at_2 := ∑' i, μ_over_d2 i

def heaviside (d e : ℕ) := ite (e < d) 0 1

def anti_heaviside (d e : ℕ) := ite (e < d) 1 0

def μ_over_d2_upto (d : ℕ) := (∑ i in finset.Ico 1 d, μ_over_d2 i)

def μ_over_d2_heaviside (d i : ℕ) := ↑(heaviside d i) * (μ_over_d2 i)

def μ_over_d2_anti_heaviside (d i : ℕ) := ↑(anti_heaviside d i) * (μ_over_d2 i)

def μ_over_d2_from (d : ℕ) := (∑' i, μ_over_d2_heaviside d i)

def one_over_d2_from (d : ℕ) := (∑' i, ↑(heaviside d i) * ((i : ℝ) ^ 2)⁻¹)

lemma asdf (d : ℕ) : μ_sum_at_2 - μ_over_d2_upto d = μ_over_d2_from d := sorry

-- Extend the sum to infinity and pick up a O(√x) term
lemma step5' :
is_Ot
sum_μ_times_n_over_d2
(λ (n : ℕ), ↑n * μ_sum_at_2)
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
at_top
:=
begin

end

lemma step5 :
is_Ot
(λ (n : ℕ), ↑n * μ_sum_at_2)
(λ (n : ℕ), ↑n * μ_over_d2_upto (sqrt n))
(λ (n : ℕ), ↑n * one_over_d2_from (sqrt n))
at_top
:=
begin
  -- unfold asymptotics.is_Ot,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 100,
  intros b hb,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  have : ↑b * μ_sum_at_2 - ↑b * μ_over_d2_upto (sqrt b) = ↑b * (μ_sum_at_2 - μ_over_d2_upto (sqrt b)), ring,
  have : |↑b * μ_sum_at_2 - ↑b * μ_over_d2_upto (sqrt b)| = |↑b| * |μ_sum_at_2 - μ_over_d2_upto (sqrt b)|, {
    simp [abs_mul, this],
  },
  rw this,
  rw asdf,
  apply mul_le_mul,
  have : |(b : ℝ)| = b, {
    simp [abs_nonneg],
  },
  rw this,
  {
    unfold μ_over_d2_from,
    unfold one_over_d2_from,
    have : |∑' (i : ℕ), μ_over_d2_heaviside (sqrt b) i| ≤ ∑' (i : ℕ), |μ_over_d2_heaviside (sqrt b) i|, {
      exact abs_tsum_le_tsum_abs (μ_over_d2_heaviside (sqrt b)),
    },
    have : ∀ (x : ℕ), (λ i, ∥μ_over_d2_heaviside (sqrt b) i∥) x ≤ (λ i, ↑(heaviside (sqrt b) i) * (↑i ^ 2)⁻¹) x, {
      intros x,
      simp,
      unfold μ_over_d2_heaviside,
      unfold heaviside,
      by_cases x < sqrt b,
      simp [h],
      simp [h],
      unfold μ_over_d2,
      simp [abs_mu_le_one],
      have : ((x : ℝ) ^ 2)⁻¹ = 1 * ((x : ℝ) ^ 2)⁻¹, simp,
      conv {
        to_rhs,
        rw this,
      },
      apply mul_le_mul,
      {
        simp [real.norm_eq_abs, abs_mu_le_one, μ],
        sorry,  -- lift to ℝ ?
      },
      exact rfl.le,
      simp [inv_nonneg, pow_nonneg],
      linarith,
    },
    -- keep going
  },
  exact abs_nonneg _,
  simp [hb],
end

lemma abs_tsum_nonneg_eq_tsum
{f : ℕ → ℝ}
(hf : ∀ (n : ℕ), 0 ≤ f n)
:
|∑' (i : ℕ), f i| = ∑' (i : ℕ), f i
:=
begin
  by_cases h : summable f,
  obtain ⟨c, hc⟩ := h,
  rw has_sum.tsum_eq hc,
  apply abs_of_nonneg,
  exact has_sum_mono has_sum_zero hc hf,
  unfold tsum,
  simp [h],
end

lemma step6 :
asymptotics.is_O
(λ (x : ℝ), x * ∑' (i : ℕ), (λ (j : ℕ), ite (x < ↑j) ((j : ℝ) ^ 2)⁻¹ 0) i)
(λ (x : ℝ), x ^ ((1 : ℝ) / 2))
at_top
:=
begin
  unfold asymptotics.is_O,
  use 1,
  unfold asymptotics.is_O_with,
  simp,
  use 200,
  intros b hb,
  rw [real.norm_eq_abs, real.norm_eq_abs, real.norm_eq_abs],
  have : |∑' (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0| ≤ ∑' (i : ℕ), |ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0|,
  exact abs_tsum_le_tsum_abs (λ (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0),
  have : ∑' (i : ℕ), |ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0| = ∑' (i : ℕ), ite (b < ↑i) ((i : ℝ) ^ 2)⁻¹ 0,
  congr,
  funext,
  simp,
  by_cases b < ↑i,
  simp [h],
  simp [h],

end