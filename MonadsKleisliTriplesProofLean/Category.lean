namespace CategoryLib

universe u v

/- Category Definition.

    A category consist of:
      •) An objects class 'obj'.
      •) ∀ a, b ∊ 'obj', an arrows class 'hom(a, b)'. -/
class Category (obj : Type u) (hom : obj → obj → Type v) where
  /- •) ∀ a ∊ 'obj', an arrow 'id(a)' ∊ 'hom(a, a)'. -/
  id : ∀ a : obj, hom a a

  /- •) ∀ a, b, c ∊ 'obj', the arrows composition operator 'comp': 'hom(b, c)' → 'hom(a, b)' → 'hom(a, c)' -/
  comp : ∀ {a b c : obj}, hom b c → hom a b → hom a c

  /- That fulfill the following:
  ⋆) 'comp' operator is associative. -/
  asoc : ∀ {a b c d : obj}
    (f : hom a b) (g : hom b c) (h : hom c d), comp h (comp g f) = comp (comp h g) f

  /- ⋆) 'id' is neutral, on the left and on the right, for the 'comp' operator. -/
  id_left :  ∀ {a b : obj} (f : hom a b), comp (id b) f = f
  id_right : ∀ {a b : obj} (f : hom a b), comp f (id a) = f


infixr:80 " ° " => Category.comp

/- CATEGORY EXAMPLES -/

/-
  The Lean Category.

  Objects are Lean types and arrows are λ-functions. Proving this is trivial.
-/
namespace LeanCategory

instance Lean_Category : Category (Type u) (fun a b => a → b) where
  id _       := fun x => x
  comp g f   := fun x => g (f x)
  asoc _ _ _ := rfl
  id_left _  := rfl
  id_right _ := rfl

end LeanCategory

namespace MonoidCategory

/-
  A monoid is a triple (M, •, e) where •:MxM→M is an associative operator
  and 'e' is neutral for •.
-/
class Monoid (M : Type u) (dot : M → M → M) (e : M) : Prop where
  asocc   : ∀ x y z : M, dot x (dot y z) = dot (dot x y) z
  e_left  : ∀ x, dot e x = x
  e_right : ∀ x, dot x e = x

/- Singleton type 'P' -/
inductive P : Type where | Point

/-
  Monoid as a one-object category.

  This category has only one object (the type 'P'). An arrow in this
  category is a monoid element. Neutral element in the monoid is the
  identity arrow on this category. To compose arrows is to compose elements
  by using the monoid operation. The proof is completed by the monoid axioms.
-/
@[instance_reducible]
def Monoid_Category
  {M : Type u} (dot : M → M → M) (e : M) [Mon : Monoid M dot e] : Category P (fun _ _ => M) where
    id _ := e
    comp := dot
    asoc f g h := Mon.asocc h g f
    id_left := Mon.e_left
    id_right := Mon.e_right

end MonoidCategory

end CategoryLib
