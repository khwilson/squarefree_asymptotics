import analysis.p_series
import number_theory.arithmetic_function
import algebra.squarefree
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

-- Lemmas
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
  sorry,
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

lemma is_multiplicative_tμ : arithmetic_function.is_multiplicative tμ :=
begin
  unfold tμ,
  apply is_multiplicative_sμ.mul,
  simp [arithmetic_function.is_multiplicative_zeta, arithmetic_function.is_multiplicative.nat_cast],
end


lemma is_square_prime_pow_iff_pow_even : ∀ (p i : ℕ), nat.prime p → (is_square (p ^ i) ↔ even i) := begin
  intros p i hp,
  split,
  unfold is_square,
  intros h,
  cases h with s hs,
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
  unfold even,
  intros h,
  cases h with k hk,
  use p ^ k,
  rw hk,
  rw ← pow_add,
  simp,
  rw ← exp_eq_iff_pow_eq (two_le_prime hp),
  ring,
end

lemma foo : ∀ (p i : ℕ), nat.prime p → 3 ≤ i → sμ (p ^ i) = 0 :=
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

lemma Ico_eq_range {n : ℕ} : finset.Ico 0 n = finset.range n :=
begin
  simp,
end

lemma finset.union_singleton {n : ℕ} {s : finset ℕ} : s ∪ {n} = insert n s :=
begin
  ext,
  rw [mem_union, mem_insert, mem_singleton, or_comm],
end

lemma tmp : ∀ (p i : ℕ), 2 ≤ p → 2 ≤ i → ¬squarefree (p^i) :=
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

lemma not_is_square_prime {p : ℕ} (hp : nat.prime p) : ¬ is_square p :=
begin
  by_contradiction H,
  rcases H with ⟨ s, hs ⟩,
  have : s ∣ p,
    calc s ∣ s * s : dvd_mul_left s s
      ... = p : hs,
  rw dvd_prime hp at this,
  cases this,
  simp [this] at hs,
  rw ← hs at hp,
  exact not_prime_one hp,
  have p_sq : squarefree p, exact prime_squarefree hp,
  unfold squarefree at p_sq,
  have foo : s * s ∣ p,
    calc s * s ∣ s * s : by simp
      ... = p : hs,
  specialize p_sq s foo,
  simp at p_sq,
  rw ← this at hp,
  rw p_sq at hp,
  exact not_prime_one hp,
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

lemma ssqrt_eq {n : ℕ} : ssqrt (n * n) = n :=
begin
  unfold ssqrt,
  rw sqrt_eq,
  unfold is_square,
  simp,
end

lemma moebius_of_prime {p : ℕ} (hp : nat.prime p) : μ p = -1 :=
begin
  rw arithmetic_function.moebius_apply_of_squarefree (prime_squarefree hp),
  rw arithmetic_function.card_factors_eq_one_iff_prime.mpr hp,
  ring,
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

lemma squarefree_nat_eq_tμ : squarefree_nat = tμ :=
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
