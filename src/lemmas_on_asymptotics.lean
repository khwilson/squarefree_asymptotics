import defs

noncomputable theory
open nat finset function filter
open_locale classical topological_space interval big_operators filter asymptotics arithmetic_function

namespace squarefree_sums

-- If f = g + O(h) and g = k + O(h') then f = k + O(h + h')
theorem is_Ot_transitive_diff {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (h' : α → ℝ) (k : α → ℝ) (l : filter α) :
is_Ot f g h l → is_Ot g k h' l → is_Ot f k (h + h') l :=
begin
  sorry,
end

-- If f = g + O(h) and g = k + O(h) then f = k + O(h)
theorem is_Ot_transitive {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (k : α → ℝ) (l : filter α) :
is_Ot f g h l → is_Ot g k h l → is_Ot f k h l :=
begin
  sorry,
end


-- Can replace the error with a bigger error
theorem is_Ot_transitive' {α : Type*} (f : α → ℝ) (g : α → ℝ) (h : α → ℝ) (k : α → ℝ) (l : filter α) :
is_Ot f g h l → asymptotics.is_O h k l → is_Ot f g k l :=
begin
  sorry,
end



end squarefree_sums
