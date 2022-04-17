import algebra.big_operators.ring
import topology.algebra.infinite_sum
import number_theory.arithmetic_function
import data.complex.basic
import analysis.special_functions.pow
import analysis.normed.group.infinite_sum
import order.filter.basic
import order.filter.at_top_bot
import analysis.calculus.fderiv

open finset filter
open_locale big_operators arithmetic_function

variables {α : Type*} [add_comm_monoid α]

def head_sum (f : ℕ → α) : (ℕ → α) := (λ n : ℕ, ∑ i in range n, f i)

variables [topological_space α]

def nat_summable (f : ℕ → α) : Prop := ∃ (a : α), tendsto (head_sum f) at_top (nhds a)

namespace nat
namespace arithmetic_function
variables {R : Type*} [has_zero R] [has_abs R]
(f : arithmetic_function ℤ) (r : ℝ) (s t : ℂ)

/-! A Dirichlet series of a function `f` at `s` is itself a function from `ℕ` to `ℂ`
which returns the `n`th term of the sum ∑ (f n) / n ^ s -/
noncomputable def dirichlet_series := (λ n : ℕ, ↑(f n) / ((n : ℂ) ^ s))

noncomputable def dirichlet_series' := ∑' i, (λ n : ℕ, ↑(f n) / ((n : ℂ) ^ s)) i

namespace dirichlet_series
localized "notation `D` := nat.arithmetic_function.dirichlet_series" in dirichlet_series
localized "notation `D'` := nat.arithmetic_function.dirichlet_series'" in dirichlet_series

/-! ### Definitions of convergence -/
/-- The Diriclet series is convergent at a point -/
def is_convergent_at : Prop := nat_summable (D f s)

/-- The Dirichlet series is convergent in a right half-plane -/
def is_convergent : Prop := ∀ s : ℂ, r < s.re → is_convergent_at f s

/-- The Dirichlet series is absolutely convergent at a point -/
def is_abs_convergent_at : Prop := summable (D f s)

/-- The Dirichlet series is absolutely convergent in a right half-plane -/
def is_abs_convergent : Prop := ∀ s : ℂ, r < s.re → is_abs_convergent_at f s

/-- The traditional definition of absolutely convergent. Equivalent to our notion of
absolute convergence. See `is_abs_convergent_at_iff_is_norm_convergent_at` -/
def is_norm_convergent_at : Prop := summable (λ n : ℕ, ∥(D f s) n ∥)

/-- The traditional definition of absolutely convergent on a right half-plane.
Equivalent to our notion of
absolute convergence. See `is_abs_convergent_iff_is_norm_convergent` -/
def is_norm_convergent : Prop := ∀ s : ℂ, r < s.re → is_norm_convergent_at f s

/-! ### Relationships between the various convergence modes

Currently enumerating the main theorems which will be turned into
many more useful lemmas later
-/

/-- The notion of norm convergence and absolute convergence are equivalent -/
lemma is_abs_convergent_at_iff_is_norm_convergent_at : is_abs_convergent_at f s ↔ is_norm_convergent_at f s :=
begin
  sorry,
end

/-- The notion of norm convergence and absolute convergence are equivalent, but
sometimes one may be easier to use than the other -/
lemma is_abs_convergent_iff_is_norm_convergent : is_abs_convergent f r ↔ is_norm_convergent f r :=
begin
  sorry,
end

/-- Convergence at a point implies convergence to the right of that point -/
lemma is_covergent_of_is_convergent_at
(hfs : is_convergent_at f s) :
is_convergent f s.re :=
begin
  sorry
end

/-- Absolute convergence at a point implies absolute convergence to the right of that point -/
lemma is_abs_covergent_of_is_abs_convergent_at
(hfs : is_abs_convergent_at f s) :
is_abs_convergent f s.re :=
begin
  sorry
end

/-- Norm convergence at a point implies norm convergence to the right of that point -/
lemma is_norm_covergent_of_is_norm_convergent_at
(hfs : is_norm_convergent_at f s) :
is_norm_convergent f s.re :=
begin
  sorry
end

/-- Convergence implies absolute convergence eventually -/
lemma is_abs_convergent_of_is_convergent
(hfs : is_convergent f r) :
is_abs_convergent f (r + 1) :=
begin
  sorry
end

/-- Convergence implies holomorphic on the open right half-plane -/
noncomputable lemma differentiable_at_of_is_convergent
(hfs : is_convergent f r) (hs : r < s.re) :
differentiable_at ℂ (D' f) s :=
begin
  sorry,
end

/-! ### Proving convergence -/

lemma is_abs_convergent_of_eventually_bounded
(hf : ∀ᶠ (n : ℕ) in at_top, ↑|f n| ≤ r) : is_abs_convergent f 1 :=
begin
  sorry
end

-- lemma is_norm_convergent_at.of_is_norm_convergent_at_re_le
-- (hfs : is_norm_convergent_at f s) (hst : s.re ≤ t.re) : is_norm_convergent_at f t :=
-- begin
--   unfold is_norm_convergent_at,
--   unfold dirichlet_series,
--   refine summable_of_norm_bounded _ hfs _,
--   unfold dirichlet_series,
--   intros i,
--   by_cases hi : i = 0,
--   { simp [hi], },
--   rw real.norm_eq_abs, rw complex.norm_eq_abs, rw complex.norm_eq_abs, rw complex.abs_abs,
--   rw complex.abs_div, rw complex.abs_div,
--   apply div_le_div,
--   exact complex.abs_nonneg _,
--   exact rfl.le,
--   rw complex.abs_pos,
--   intros h,
--   rw complex.cpow_eq_zero_iff at h,
--   rcases h with ⟨hi', _⟩,
--   norm_cast at hi',
--   have : 1 ≤ i, exact one_le_iff_ne_zero.mpr hi,
--   have : 0 < i, linarith [this],
--   have aa : 0 < (i : ℝ), { norm_cast, exact this, },
--   have bb : (i : ℂ) = ((i : ℝ) : ℂ), simp,
--   rw bb,
--   rw complex.abs_cpow_eq_rpow_re_of_pos aa,
--   rw complex.abs_cpow_eq_rpow_re_of_pos aa,
--   refine real.rpow_le_rpow_of_exponent_le _ hst,
--   norm_cast,
--   exact one_le_iff_ne_zero.mpr hi,
-- end

-- lemma is_abs_convergent_at.of_is_abs_convergent_at_re_le
-- (hfs : is_abs_convergent_at f s) (hst : s.re ≤ t.re) : is_abs_convergent_at f t :=
-- begin
--   rw is_abs_convergent_at_iff_is_norm_convergent_at at hfs,
--   rw is_abs_convergent_at_iff_is_norm_convergent_at,
--   exact hfs.of_is_norm_convergent_at_re_le f s t hst,
-- end

lemma is_abs_convergent_of_eventually_bounded (c : ℕ) (hc : ∀ᶠ (x : ℕ) in at_top, |f x| ≤ c) : is_abs_convergent f 1 :=
begin
  sorry,
end

lemma is_abs_convergent_of_bounded (c : ℕ) (hc : ∀ (i : ℕ), |f i| ≤ c) : is_abs_convergent f 1 :=
begin
  refine is_abs_convergent_of_eventually_bounded f c _,
  apply eventually_of_forall,
  simp [hc],
end

theorem zeta.is_abs_convergent : is_abs_convergent ζ 1 :=
begin
  refine is_abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [zeta],
  by_cases hi : i = 0,
  simp [hi],
  simp [hi],
end

theorem moebius.is_abs_convergent : is_abs_convergent μ 1 :=
begin
  refine is_abs_convergent_of_bounded _ 1 _,
  intros i,
  simp [moebius],
  by_cases hi : squarefree i,
  simp [hi],
  simp [hi],
end



end dirichlet_series
end arithmetic_function
end nat