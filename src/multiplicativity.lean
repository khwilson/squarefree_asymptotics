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

lemma is_multiplicative_ssqrt {a b : ℕ} (hab : a.coprime b) : ssqrt (a * b) = (ssqrt a) * (ssqrt b) :=
begin
  by_cases ha : square a,
  {
    by_cases hb : square b,
    {
      have : square (a * b), exact prod_squares_square ha hb,
      unfold ssqrt,
      simp [ha, hb, this],
      cases ha with a' ha',
      cases hb with b' hb',
      rw pow_two at ha',
      rw pow_two at hb',
      rw [ha', hb'],
      rw [sqrt_eq, sqrt_eq],
      have : a' * a' * (b' * b') = (a' * b') * (a' * b'), ring,
      rw this,
      rw sqrt_eq,
    },
    {
      have : ¬square (a * b), exact coprime_prod_not_squares_is_not_square' hab hb,
      unfold ssqrt,
      simp [ha, hb, this],
    },
  },
  {
    have : ¬square (a * b), exact coprime_prod_not_squares_is_not_square hab ha,
    unfold ssqrt,
    simp [ha, this],
  },
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
    simp [square_one],
  },
  {
    intros m n hmn,
    unfold sμ,
    simp,
    unfold sμ',
    have : ssqrt (m * n) = (ssqrt m) * (ssqrt n), exact is_multiplicative_ssqrt hmn,
    rw this,
    by_cases hm : square m,
    {
      by_cases hn : square n,
      {
        have : (ssqrt m).coprime (ssqrt n), exact coprime_ssqrt hm hn hmn,
        simp [arithmetic_function.is_multiplicative_moebius, this],
      },
      {
        unfold ssqrt,
        have : ¬square (m * n), exact coprime_prod_not_squares_is_not_square' hmn hn,
        simp [hm, hn, this],
      },
    },
    {
      unfold ssqrt,
      have : ¬square (m * n), exact coprime_prod_not_squares_is_not_square hmn hm,
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
      have : squarefree (m * n), exact (squarefree_mul h).mpr ⟨hm, hn⟩,
      simp [this, hm, hn],
    },
    {
      have : ¬squarefree (m * n), {
        intros H,
        exact hn H.of_mul_right,
      },
      simp [this, hm, hn],
    },
  },
  {
    have : ¬squarefree (m * n), {
      intros H,
      exact hm H.of_mul_left,
    },
    simp [this, hm],
  },
end

end squarefree_sums