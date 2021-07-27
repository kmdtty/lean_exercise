variables {X Y Z : Type}


-- def comp (f : Y → Z) (g: X → Y) : X → Z :=
-- λx, f(g x)

-- infixr ` ∘ ` := comp

-- def id (x: X) : X := 
-- x

-- funext is function extensionality (what?)
example (f g : X → Y) (h: ∀ x, f x = g x) : f = g:=
funext h 

lemma left_id (f : X → Y) : id ∘ f = f := 
rfl

lemma right_id (f: X → Y) : f ∘ id = f := rfl
