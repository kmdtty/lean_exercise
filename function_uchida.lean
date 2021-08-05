/-
Theorems/Examples from Fuichi, Uchida "Shugo to Iso" (2020).
-/

universes u v
-- What's the difference between:
-- Sort, Sort*, Type, Type* ?
variables {A B C W X Y Z α β: Sort*}

def injective (f: X → Y) : Prop :=
 ∀ ⦃x₁ x₂⦄ , f(x₁) = f(x₂) → x₁ = x₂

def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y

theorem injective_id : injective(@id X) :=
sorry

theorem injective_comp {f: X → Y} {g: Y→ Z}
(hg: injective f) (hg: injective g) :
injective (g ∘ f) :=
sorry

/--
 Theorem 6.1: 
  Let f: A → B, g : B → A,
  f ∘ g = id B → surgective f ∧ injective g. 
-/
theorem id_comp_surj_inj 
  {f: A → B} {g: B → A} : 
  f ∘ g = (@id B) →  surjective f ∧ injective g:=
assume a : A,
assume b₁ (hb1: g b₁ = a),
assume b₂ (hb2: (f ∘ g) b₁ = b₂),
assume h1: (f ∘ g) b₁ = id b₂,
have h2: f (g b₁) = b₂, from h1,
sorry
--show ∃ b₁, f (g b₁) = b₂, from exists.intro b₁ h2


/-
Exercise 6.2
Let f: A→B, g: B→C
(1) If g ∘ f is injective, f is injective
(2) If g ∘ f is surjective, g is surjective
-/

-- (1)
theorem comp_injective_1st 
{f: A → B} {g: B → C} :
injective(g ∘ f) → injective f :=
sorry

--(2)
theorem comp_surjective_2nd
{f: A → B} {g: B → C} :
surjective(g ∘ f) → surjective g :=
sorry
