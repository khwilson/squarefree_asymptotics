import number_theory.arithmetic_function
import algebra.squarefree
import algebra.order.floor
import data.list.intervals
import tactic
import measure_theory.integral.interval_integral
import general
import defs
import lemmas_on_defs

noncomputable theory
open nat finset function filter
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums
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
      simp [hm, this],
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

/-
This lemma is _nearly_ identical to nat.multiplicative_factorization.
However, that lemma requires f 0 = 1 whereas arithmetic_function requires
f 0 = 0.

The proof can probably be much simpler, but it's mostly futzing around with
the differences between multisets and lists and finsupps etc.
-/
lemma multiplicative_eq_iff_eq_on_prime_powers {f g : arithmetic_function ℤ}
(hf : f.is_multiplicative)
(hg : g.is_multiplicative)
:
f = g ↔ ∀ (p i : ℕ), nat.prime p → f (p^i) = g (p^i)
:=
begin
  split,
  intros h p i _,
  simp [h],
  intros h,
  ext n,
  by_cases hn : n = 0,
  rw [hn, arithmetic_function.map_zero, arithmetic_function.map_zero],
  rw nat.multiplicative_factorization f (λ x y, (λ hxy, hf.map_mul_of_coprime hxy)) hf.map_one hn,
  rw nat.multiplicative_factorization g (λ x y, (λ hxy, hg.map_mul_of_coprime hxy)) hg.map_one hn,

  have : n.factorization.support ⊆ n.factors.to_finset, simp,
  rw finsupp.prod_of_support_subset n.factorization this,
  rw finsupp.prod_of_support_subset n.factorization this,
  apply prod_congr rfl,
  intros p hp,
  rw list.mem_to_finset at hp,
  exact h p (n.factorization p) (nat.prime_of_mem_factors hp),

  intros i hi, rw pow_zero, exact hg.map_one,
  intros i hi, rw pow_zero, exact hf.map_one,
end

end squarefree_sums