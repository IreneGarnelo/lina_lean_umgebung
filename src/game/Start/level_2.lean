-- Level name : Start - Mache hier weiter

import data.nat.basic -- hide

/-
Hier ist ein eiführender Text
-/

/- Theorem
$a+0=a$
-/
theorem add_null (a : nat) : a + 0 = a :=
begin
  exact nat.add_zero a,
end