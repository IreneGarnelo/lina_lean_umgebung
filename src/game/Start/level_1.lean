-- Level name : Start - Fange hier an

import data.nat.basic -- hide

/-
Hier ist ein eiführender Text
-/

/- Theorem
$a+b=b+a$
-/
theorem add_komm (a b : nat) : a + b = b + a :=
begin
  exact nat.add_comm a b,
end