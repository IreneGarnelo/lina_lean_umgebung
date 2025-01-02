-- Level name : Fortsetzung

import data.nat.basic -- hide

/-
Hier ist ein eiführender Text
-/

/- Theorem
$a ⬝ (b ⬝ c) = (a \cdot b ) ⬝ c $
-/
theorem mul_assoz (a b c : nat) : (a * b) * c = a * (b * c) :=
begin
  exact nat.mul_assoc a b c,
end