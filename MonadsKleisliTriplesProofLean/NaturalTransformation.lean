import MonadsKleisliTriplesProofLean.Functor

namespace NaturalTransformationLib

open CategoryLib

universe u v u₁ v₁

/-
  Natural Transformation Definition.
  While functors are arrows between categories, natural transformations are
  arrows between functors.
  Given two functors F₁, F₂ : C → D, a natural transformation F₁⇒F₂ is, for each
  x ∊ Obj(C), to give an arrow η(x) : Fobj(x) → Gobj(x).
-/
class NatTransf
  {objC : Type u}  {homC : objC → objC → Type v}  [C : Category objC homC]
  {objD : Type u₁} {homD : objD → objD → Type v₁} [D : Category objD homD]
  {Fobj Gobj : objC → objD} {F : ∀ {a b : objC}, homC a b → homD (Fobj a) (Fobj b)} {G : ∀ {a b : objC}, homC a b → homD (Gobj a) (Gobj b)}
  (F1 : FunctorLib.Functor Fobj F)
  (F2 : FunctorLib.Functor Gobj G)
  (η : ∀ x : objC, homD (Fobj x) (Gobj x)) : Prop where
  /- That fulfill the following:, for each f:a → b,

             F(f)
    F(a) ------------> F(b)
     |                  |
     |                  |
     |η(a)              |η(b)
     |                  |
     |                  |
     v       G(f)       v
    G(a) ------------> G(b)
  -/
  η_law : ∀ {a b : objC} (f : homC a b), (G f) ° (η a) = (η b) ° (F f)

end NaturalTransformationLib
