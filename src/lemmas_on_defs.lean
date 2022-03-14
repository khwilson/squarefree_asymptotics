import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general
import defs

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

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
  have two_le_p : 2 ≤ p, exact hp.two_le,
  rw ← exp_eq_iff_pow_eq two_le_p at hs,
  use k,
  rw ← hs,
  ring,

  rintros ⟨k, hk⟩,
  use p ^ k,
  rw hk,
  rw ← pow_add,
  simp,
  rw ← exp_eq_iff_pow_eq hp.two_le,
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

lemma ssqrt_one : ssqrt 1 = 1 :=
begin
  unfold ssqrt,
  simp [is_square_one],
  exact sqrt_one_eq_one,
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
  have : is_square (n * n), {
    use n,
  },
  simp [this],
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

lemma coprime_prod_not_squares_is_not_square {a b : ℕ} (hab : a.coprime b) (ha : ¬ is_square a) : ¬ is_square (a * b) :=
begin
  by_contradiction H,
  unfold is_square at H,
  rcases H with ⟨s, hs⟩,
  have : a = (s.gcd a) * (s.gcd a), {
    exact (nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul hab hs).symm,
  },
  unfold is_square at ha,
  push_neg at ha,
  exact (ha $ s.gcd a).symm this,
end

lemma coprime_prod_not_squares_is_not_square' {a b : ℕ} (hab : a.coprime b) (hb : ¬ is_square b) : ¬ is_square (a * b) :=
begin
  rw mul_comm,
  have hab' : b.coprime a, exact (coprime_comm.mp) hab,
  exact coprime_prod_not_squares_is_not_square hab' hb,
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


end squarefree_sums
