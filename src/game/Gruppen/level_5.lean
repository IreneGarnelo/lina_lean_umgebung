-- Level name : Falls Inverse kommutieren, dann ist $G$ abelsch

import algebra.group.basic -- hide

/- Wir werden uns nun folgendes Lemma anschauen, welches wir in der letzten Aufgabe
anwenden werden. Du musst diesen Beweis nicht selber führen, sondern kannst ihr
einfach mithilfe der Lean-Ausgabe nachvollziehen:
```
intros x y,
  specialize h x y,
  have h1 : (x⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * x⁻¹)⁻¹, from congr_arg has_inv.inv h,
  rw mul_inv_rev x⁻¹ y⁻¹ at h1,
  rw mul_inv_rev y⁻¹ x⁻¹ at h1,
  repeat {rw inv_inv at h1,},
  exact h1.symm,
```
Du musst nicht alle Keywörter wie `specialize` und `congr_arg` kennen. Kannst du trotzdem für jeden
Schritt beschreiben was passiert?
 -/

-- Theorem: Falls $x^{-1} \cdot y^{-1} = y^{-1} \cdot x^{-1}$ für alle $x,y \in G$, dann ist $G$ abelsch.
theorem inv_abelsch {G : Type} [group G]
  (h : ∀ x y : G, x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹) :
  ∀ x y : G, x * y = y * x :=
begin
  intros x y,
  -- Start with the given condition for x⁻¹ and y⁻¹
  specialize h x y,
  -- Take the inverse of both sides
  have h1 : (x⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * x⁻¹)⁻¹, from congr_arg has_inv.inv h,
  -- Use the property (a * b)⁻¹ = b⁻¹ * a⁻¹ on both sides
  rw mul_inv_rev x⁻¹ y⁻¹ at h1,
  rw mul_inv_rev y⁻¹ x⁻¹ at h1,
  repeat {rw inv_inv at h1,},
  exact h1.symm,




  
end
