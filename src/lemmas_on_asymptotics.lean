import defs

noncomputable theory
open nat finset function filter asymptotics
open_locale topological_space interval big_operators filter asymptotics arithmetic_function

-- h and h' are errors
variables {α : Type*} {f : α → ℝ} {g : α → ℝ} {h : α → ℝ} {h' : α → ℝ} {k : α → ℝ} {l : filter α}

namespace squarefree_sums

lemma is_Ot_comm : is_Ot f g h l ↔ is_Ot g f h l :=
begin
  unfold is_Ot,
  split,
  rintros ⟨c, hc⟩,
  use c,
  unfold is_O_with,
  unfold is_O_with at hc,
  simp,
  simp at hc,
  conv {
    congr,
    funext,
    rw real.norm_eq_abs,
    rw abs_sub_comm,
    rw ← real.norm_eq_abs,
  },
  exact hc,

  rintros ⟨c, hc⟩,
  use c,
  unfold is_O_with,
  unfold is_O_with at hc,
  simp,
  simp at hc,
  conv {
    congr,
    funext,
    rw real.norm_eq_abs,
    rw abs_sub_comm,  -- No norm_sub_comm?
    rw ← real.norm_eq_abs,
  },
  exact hc,
end

-- If f = g + O(h) and g = k + O(h) then f = k + O(h)
theorem is_Ot_trans_same_error :
is_Ot f g h l → is_Ot g k h l → is_Ot f k h l :=
begin
  unfold is_Ot,
  unfold is_O_with,
  rintros ⟨c, hc⟩,
  rintros ⟨d, hd⟩,
  use (c + d),
  simp at hc,
  simp at hd,
  rw eventually_iff_exists_mem,
  rw eventually_iff_exists_mem at hc,
  rw eventually_iff_exists_mem at hd,
  rcases hc with ⟨v, hv, hv'⟩,
  rcases hd with ⟨w, hw, hw'⟩,
  let V := v ∩ w,
  have hV : V ∈ l, simp [hv, hw],
  use V, split, exact hV,
  intros y hy,
  have hy_v : y ∈ v, calc y ∈ V : hy ... ⊆ v : by simp,
  have hy_w : y ∈ w, calc y ∈ V : hy ... ⊆ w : by simp,
  specialize hv' y hy_v,
  specialize hw' y hy_w,
  rw [real.norm_eq_abs, real.norm_eq_abs] at hv',
  rw [real.norm_eq_abs, real.norm_eq_abs] at hw',
  rw [real.norm_eq_abs, real.norm_eq_abs],
  simp,
  transitivity,
  exact abs_sub_le (f y) (g y) (k y),
  transitivity,
  exact add_le_add hv' hw',
  apply le_of_eq,
  ring,
end

lemma ughugh {a b : ℝ} :
a < 0 → 0 ≤ b → a * b ≤ 0 :=
begin
  intros ha hb,
  rw mul_nonpos_iff,
  right,
  split,
  exact le_of_lt ha,
  exact hb,
end

lemma is_O_with_abs {c : ℝ} :
is_O_with c f h l → is_O_with (|c|) f h l :=
begin
  unfold is_O_with,
  rw eventually_iff_exists_mem,
  rw eventually_iff_exists_mem,
  rintros ⟨v, hv, hv'⟩,
  use v, simp [hv],
  intros y hy,
  specialize hv' y hy,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs,
  rw real.norm_eq_abs at hv',
  rw real.norm_eq_abs at hv',
  by_cases hc : 0 ≤ c,
    rw abs_of_nonneg hc,
    exact hv',

    push_neg at hc,
    have boo : c * |h y| ≤ 0, exact ughugh hc (abs_nonneg (h y)),
    have : 0 ≤ |f y|, exact abs_nonneg (f y),
    have : |f y| ≤ 0, calc |f y| ≤ c * |h y| : hv' ... ≤ 0 : boo,
    have : |f y| = 0, linarith,
    rw this,
    rw ← abs_mul,
    exact abs_nonneg (c * h y),
end

-- Can replace the error with a bigger error
theorem is_Ot_bigger_error :
is_Ot f g h l → asymptotics.is_O h h' l → is_Ot f g h' l :=
begin
  rintros ⟨c, hc⟩,
  intros hh',
  rw is_O_iff_is_O_with at hh',
  rcases hh' with ⟨c', hc'⟩,
  unfold is_Ot,
  use |c| * c',
  exact is_O_with.trans (is_O_with_abs hc) hc' (abs_nonneg c),
end

theorem is_Ot_trans_bigger_error_left :
is_Ot f g h l → is_Ot g k h' l → is_O h h' l → is_Ot f k h' l :=
begin
  intros hfg hgk hhh',
  exact is_Ot_trans_same_error (is_Ot_bigger_error hfg hhh') hgk,
end

theorem is_Ot_trans_bigger_error_right :
is_Ot f g h' l → is_Ot g k h l → is_O h h' l → is_Ot f k h' l :=
begin
  intros hfg hgk hhh',
  exact is_Ot_trans_same_error hfg (is_Ot_bigger_error hgk hhh'),
end

lemma is_Ot.congr
(hfg : f = g) :
is_Ot f g h l
:=
begin
  unfold is_Ot,
  use 0,
  unfold is_O_with,
  simp [hfg],
end

end squarefree_sums
