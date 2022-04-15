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
open nat finset function filter nat.arithmetic_function
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

def arithmetic_function.from_pred {p : ℕ → Prop} [decidable_pred p] (hp : ¬p 0) :
arithmetic_function ℕ :=
⟨(λ (n : ℕ), ite (p n) (1 : ℕ) 0), by simp only [hp, if_false]⟩


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

lemma blah {α : Sort*} {a b : α} : a = b ↔ b = a := ⟨(λ h, h.symm), (λ h, h.symm)⟩

lemma square_iff_sqrt_mul_sqrt_eq {m : ℕ} : square m ↔ (sqrt m) * (sqrt m) = m :=
begin
  rw ←pow_two,
  convert m.exists_mul_self',
  conv { to_rhs, congr, funext, rw blah, },
  refl,
end

lemma square_iff_ssqrt_mul_ssqrt_eq {m : ℕ} : square m ↔ (ssqrt m) * (ssqrt m) = m :=
begin
  split,
  { intros h,
    simp only [ssqrt, h, if_true],
    exact square_iff_sqrt_mul_sqrt_eq.mp h, },
  { contrapose!,
    intros h,
    simp only [ssqrt, h, if_false, mul_zero],
    intros h',
    rw ←h' at h,
    exact h square_zero, },
end

lemma sqrt_dvd_of_square {m : ℕ} : square m → (sqrt m ∣ m) :=
begin
  intros hm,
  rw [←square_iff_sqrt_mul_sqrt_eq.mp hm, sqrt_eq],
  exact dvd_mul_left _ _,
end

lemma ssqrt_dvd_of_square {m : ℕ} : square m → (ssqrt m ∣ m) :=
begin
  intros hm,
  simp only [ssqrt, hm, if_true],
  exact sqrt_dvd_of_square hm,
end

lemma is_multiplicative_sμ : arithmetic_function.is_multiplicative sμ :=
begin
  -- This proof doesn't quite work out as neatly as other multiplicative proofs because
  -- while moebius is multiplicative and ssqrt is multiplicative, it is _not_ true that
  -- (ssqrt m).coprime (ssqrt n) in general. Indeed, if m and n are both not squares,
  -- then this will be false (`not_coprime_zero_zero`).
  rw is_multiplicative.iff_ne_zero,
  split,
  { simp only [sμ, sμ', zero_hom.coe_mk, ssqrt_one, is_multiplicative_moebius.left], },
  { intros m n hm hn hmn,
    simp only [sμ, sμ', zero_hom.coe_mk],
    by_cases hm_square : square m,
    { by_cases hn_square : square n,
      { rw [← is_multiplicative_moebius.right, ←is_multiplicative_ssqrt hmn],
        refine nat.coprime.coprime_dvd_left (ssqrt_dvd_of_square hm_square) _,
        exact nat.coprime.coprime_dvd_right (ssqrt_dvd_of_square hn_square) hmn, },
      { have : ¬ (square m ∧ square n), simp only [hn_square, and_false, not_false_iff],
        simp [ssqrt, if_false, hn_square, (square_mul hmn).not.mpr this], }, },
    { have : ¬ (square m ∧ square n), simp only [hm_square, false_and, not_false_iff],
      simp [ssqrt, if_false, hm_square, (square_mul hmn).not.mpr this], }, },
end

lemma is_multiplicative_tμ : arithmetic_function.is_multiplicative tμ :=
begin
  unfold tμ,
  apply is_multiplicative_sμ.mul,
  simp [is_multiplicative_zeta, is_multiplicative.nat_cast],
end

lemma is_multiplicative_squarefree_nat : arithmetic_function.is_multiplicative squarefree_nat :=
begin
  rw arithmetic_function.is_multiplicative.iff_ne_zero,
  split,
  { simp only [squarefree_nat, squarefree_nat', zero_hom.coe_mk, squarefree_one, if_true], },
  { intros m n hm hn hmn,
    simp only [squarefree_nat, squarefree_nat', zero_hom.coe_mk, squarefree_mul hmn, ite_and],
    rw [←ite_mul_zero_left, one_mul], },
end

end squarefree_sums