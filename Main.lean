/-
  Author: Cenobio Moisés Vázquez Reyes

  This module is part of my thesis degree work named:

  «Mónadas en la programación funcional: una prueba formal de su equivalencia con las ternas de Kleisli»
  (Monads in functional programming: a formalized proof of their equivalence with Kleisli triples)
-/
import MonadsKleisliTriplesProofLean

namespace CatsMonads

universe u v

open CategoryLib NaturalTransformationLib KleisliTripleLib

/-
  Theorem: Any Kleisli triple is a monad.
-/
theorem KleisliTriple_is_Monad
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom]
  {Tobj : obj → obj} {η : ∀ a : obj, hom a (Tobj a)} [KT : KleisliTriple Tobj η] :
  MonadLib.Monad
    (KleisliTriple_is_Functor (KT := KT))
    (KleisliTriple_is_η_NT    (KT := KT))
    (KleisliTriple_es_μ_NT    (KT := KT)) where
  μ_asoc x := by
    rw [KT.kiii, Category.asoc, KT.kii, Category.id_left,
      KT.kiii, Category.id_right]
  η_left x := KT.kii _
  η_right x := by
    rw [KT.kiii, Category.asoc, KT.kii, Category.id_left, KT.ki]

/-
  Theorem: Any monad is a Kleisli triple, where f★ = μ(b)°T(f).
  The proof only use the monad definition.
-/
@[instance_reducible]
def Monad_is_KleisliTriple
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom]
  {Tobj : obj → obj} {T : ∀ {a b}, hom a b → hom (Tobj a) (Tobj b)} {TFunct : FunctorLib.Functor Tobj T}
  {η : ∀ a, hom a (Tobj a)}               {η_NT : NatTransf FunctorLib.functId TFunct η}
  {μ : ∀ a, hom (Tobj (Tobj a)) (Tobj a)} {μ_NT : NatTransf (TFunct ● TFunct) TFunct μ}
  (Mon : MonadLib.Monad TFunct η_NT μ_NT) : KleisliTriple Tobj η where
  ext := fun {a b} f => μ b ° T f
  ki a := Mon.η_right a
  kii f := by
    rw [← Category.asoc, η_NT.η_law, Category.asoc, Mon.η_left,
      Category.id_left]
  kiii {a b c} f g := by
    calc
      (μ c ° T g) ° (μ b ° T f) = μ c ° ((T g ° μ b) ° T f) := by
        simp only [Category.asoc]
      _ = μ c ° ((μ (Tobj c) ° T (T g)) ° T f) := by
        rw [μ_NT.η_law g]
      _ = (μ c ° T (μ c)) ° (T (T g) ° T f) := by
        rw [Mon.μ_asoc]
        simp only [Category.asoc]
      _ = μ c ° T ((μ c ° T g) ° f) := by
        rw [TFunct.preserv_comp, TFunct.preserv_comp]
        simp only [Category.asoc]

end CatsMonads
