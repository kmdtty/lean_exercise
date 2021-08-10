/-
Theorems/Examples from Fuichi, Uchida "Shugo to Iso" (2020).
-/

universes u v
-- What's the difference between:
-- Sort, Sort*, Type, Type* ?
variables {A B C W X Y Z α β: Sort*}

--def injective {X Y} (f : X → Y) : Prop :=
--  ∀ ⦃ x₁ x₂ ⦄, f x₁ = f x₂ → x₁ = x₂ 

def injective (f: X → Y) : Prop :=
 ∀ ⦃ x₁ x₂ ⦄ , f x₁ = f x₂ → x₁ = x₂

--@[reducible] def injective (f : α → β) : Prop := 
--∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def surjective (f: X → Y) : Prop :=
 ∀ y, ∃ x, f x = y

theorem injective_id : injective(@id X) :=
assume x₁ x₂,
assume h1: id x₁ = id x₂,
show x₁ = x₂, from h1

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
  f ∘ g = @id B →  surjective f  :=
assume b₁ b₂ : B,
assume a: A,
--assume b₁ (hb1: g b₁ = a),
--assume b₂ (hb2: (f ∘ g) b₁ = b₂),
assume h1: f ∘ g = @id B,
have h2: f (g b₁) = id b₁, from congr_fun h1 b₁,
have h3: f (g b₁) = b₁, from h2,
have hb2: ∃ a, g b₁ = a, 
show ∃a, f (a) = b₁, from congr_fun h3 hb2
--show ∃ a, f (a) = b₁, from  h4


/-
Exercise 6.2
Let f: A→B, g: B→C
(1) If g ∘ f is injective, f is injective
(2) If g ∘ f is surjective, g is surjective
-/

-- (1)
theorem comp_injective_1st 
{f: A → B} {g: B → C} :
injective (g ∘ f) → injective f :=
assume h1: injective (g ∘ f),
assume a₁ a₂ : A,
assume h4: f a₁ = f a₂,
-- Why can not say this??
-- have h5: g (f a₁) = g (f a₂), from  h4,
have h5: g (f a₁) = g (f a₂), from congr_arg g h4,
show a₁ = a₂, from h1 h5 

--(2)
theorem comp_surjective_2nd
{f: A → B} {g: B → C} :
surjective(g ∘ f) → surjective g :=
assume a : A,
assume c : C,
assume h1: surjective (g ∘ f),
have h3: ∀c, ∃ a, g (f a) = c, from h1, 
-- assume b: B,
--assume h4: b = f(a), 
let b := f(a),
show ∀c, ∃ b, g b = c,from exists.intro b h3 h4
