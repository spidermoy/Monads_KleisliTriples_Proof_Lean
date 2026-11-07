import MonadsKleisliTriplesProofLean.NaturalTransformation

namespace MonadLib

open CategoryLib NaturalTransformationLib

universe u v

/-
  Monad Definition.
 “A monad is just a monoid in the category of endofunctors, what’s the problem?”
  ̣─James Iry

  The term 'monad' was introduced by Mac Lane on 1971. Eugenio Moggi used monads
  to give semantics to functional programming languages. After, Phillip Wadler
  introduced monads on the functional programming following the Moggi's work.

  A monad (T, η, μ) over a category C consist of:
  •) A functor T:C → C.
  •) A natural transformation η: IdC ⇒ T.
  •) A natural transformation μ: T² ⇒ T.
-/
class Monad
  {obj : Type u} {hom : obj → obj → Type v} {Tobj : obj → obj} [C : Category obj hom]
  {T : ∀ {a b : obj}, hom a b → hom (Tobj a) (Tobj b)} (TFunct : FunctorLib.Functor Tobj T)
  {η : ∀ x : obj, hom x (Tobj x)}               (η_NT : NatTransf FunctorLib.functId TFunct η)
  {μ : ∀ x : obj, hom (Tobj (Tobj x)) (Tobj x)} (μ_NT : NatTransf (TFunct ● TFunct) TFunct μ) : Prop where
/- That fulfill the following:
   μ is 'asociative':

           T(μ)
    T³ -----------> T²
    |               |
    |               |
    |μ(T)           |μ
    |               |
    |               |
    v       μ       v
    T² -----------> T
  -/
  μ_asoc : ∀ x : obj, (μ x) ° (T (μ x)) = (μ x) ° (μ (Tobj x))
  /- η is 'unit' for μ

       η(T)          T(η)
   T --------> T² <-------- T
   |           |            |
   |           |            |
   |Id(T)      |μ           |Id(T)
   |           |            |
   |           |            |
   v           v            v
   T ========= T ========== T
  -/
  η_left  : ∀ x : obj, (μ x) ° (η (Tobj x)) = Category.id (Tobj x)
  η_right : ∀ x : obj, (μ x) ° (T (η x))    = Category.id (Tobj x)

end MonadLib
