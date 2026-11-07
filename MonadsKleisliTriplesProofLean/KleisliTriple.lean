import MonadsKleisliTriplesProofLean.NaturalTransformation

namespace KleisliTripleLib

open CategoryLib

universe u v

/-
 “Kleisli triples are just an alternative description for monads.”
  ─Eugenio Moggi

  A Kleisli triple (T, η, _★) over a category C consist of:
  •) A classes function T:ObjC → ObjC.
  •) For each a ∊ Obj(C), an arrow η(a): a → T(a).
  •) For each f:a → T(b), an arrow f★:T(a) → T(b).
-/
class KleisliTriple
  {obj : Type u} {hom : obj → obj → Type v} [C : outParam (Category obj hom)]
  (Tobj : obj → obj)
  (η : outParam (∀ a : obj, hom a (Tobj a))) where
  ext : ∀ {a b : obj}, hom a (Tobj b) → hom (Tobj a) (Tobj b)
/- That fulfill the following:
    •) η(a)★ = id(T(a)) -/
  ki : ∀ a : obj, ext (η a) = Category.id (Tobj a)
/- •) f★ ° η(a) = f -/
  kii : ∀ {a b : obj} (f : hom a (Tobj b)), (ext f) ° (η a) = f
/- g★ ° f★ = (g★ ° f)★ -/
  kiii : ∀ {a b c : obj} (f : hom a (Tobj b)) (g : hom b (Tobj c)), (ext g) ° (ext f) = ext ((ext g) ° f)

postfix:90 " ★" => KleisliTriple.ext (η := _)

/-
  Lemma: A Kleisli triple (T, η, _★) is a functor, where T(f) = (η(b)°f)★.
-/
theorem KleisliTriple_is_Functor
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom]
  {Tobj : obj → obj} {η : ∀ a : obj, hom a (Tobj a)} [KT : KleisliTriple Tobj η] :
  FunctorLib.Functor Tobj (fun {a b : obj} (f : hom a b) => (η b ° f) ★) := by
  constructor
/- T preserves identities. -/
  · intro a
    rw [Category.id_right, KT.ki]
/- T preserves compositions. -/
  · intro a b c f g
    rw [KT.kiii]
    simp only [Category.asoc]
    rw [KT.kii]

/-
  Lemma: A Kleisli triple (T, η, _★) is a natural transformation η: IdC ⇒ T,
         where T is the previous functor.
-/
theorem KleisliTriple_is_η_NT
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom]
  {Tobj : obj → obj} {η : ∀ a : obj, hom a (Tobj a)} [KT : KleisliTriple Tobj η] :
  NaturalTransformationLib.NatTransf FunctorLib.functId
  (KleisliTriple_is_Functor (KT := KT)) η := by
  constructor
  intro a b f
  /- For each f:a → b,

            f
    a -------------> b
    |                |
    |                |
    |η(a)            |η(b)
    |                |
    |                |
    v       T(f)     v
    T(a) ----------> T(b)
  -/
  exact KT.kii (η b ° f)

/-
  Lemma: A Kleisli triple (T, η, _★) is a natural transformation μ: T² ⇒ T,
         where T is the same previous functor and μ(x) = id(T(x))★.
-/
theorem KleisliTriple_es_μ_NT
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom]
  {Tobj : obj → obj} {η : ∀ a : obj, hom a (Tobj a)} [KT : KleisliTriple Tobj η] :
  NaturalTransformationLib.NatTransf
    ((KleisliTriple_is_Functor (KT := KT)) ● (KleisliTriple_is_Functor (KT := KT)))
    (KleisliTriple_is_Functor (KT := KT))
    (fun x : obj => (Category.id (Tobj x)) ★) := by
  constructor
  intro a b f
  /-
  For each f:a → b,

            T²(f)
  T²(a) ----------> T²(b)
    |                 |
    |                 |
    |μ(a)             |μ(b)
    |                 |
    |                 |
    v       T(f)      v
  T(a) -----------> T(b)
  -/
  rw [KT.kiii, KT.kiii, Category.id_right, Category.asoc, KT.kii, Category.id_left]

end KleisliTripleLib
