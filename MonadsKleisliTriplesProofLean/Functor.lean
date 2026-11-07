import MonadsKleisliTriplesProofLean.Category

namespace FunctorLib

open CategoryLib

universe u v u₁ v₁ u₂ v₂

/-
  Functor Definition.
  Intuitively, given two categorys C and D, a functor from C to D is an arrow
  that maps C-objects to D-objects, and C-arrows to D-arrows. In a formal way,
  a functor from C to D consist of:
   i) A function of classes Fobj:objC → objD.
   ii) ∀ a, b ∊ objC, a function of classes F:Hom(a,b) → Hom(Fobj(a), Fobj(b)).
-/
class Functor
  {objC : Type u}  {homC : objC → objC → Type v}  [C : Category objC homC]
  {objD : Type u₁} {homD : objD → objD → Type v₁} [D : Category objD homD]
  (Fobj : objC → objD)
  (F : ∀ {a b : objC}, homC a b → homD (Fobj a) (Fobj b)) : Prop where
  /- That fulfill the following:
     •) F preserves identities. -/
  preserv_id : ∀ a : objC, F (Category.id a) = Category.id (Fobj a)
  /- •) F preserves arrows composition. -/
  preserv_comp : ∀ {a b c : objC} (f : homC a b) (g : homC b c), F (g ° f) = (F g) ° (F f)


/- Identity Functor. -/
theorem functId
  {obj : Type u} {hom : obj → obj → Type v} [C : Category obj hom] :
  Functor (fun x : obj => x)
          (fun {a b : obj} (f : hom a b) => f) where
  preserv_id _ := rfl
  preserv_comp _ _ := rfl

/- Functors Composition. -/
theorem FunctComp
  {objC : Type u}  {homC : objC → objC → Type v}  [C : Category objC homC]
  {objD : Type u₁} {homD : objD → objD → Type v₁} [D : Category objD homD]
  {objE : Type u₂} {homE : objE → objE → Type v₂} [E : Category objE homE]
  {Gobj : objD → objE} {G : ∀ {a b : objD}, homD a b → homE (Gobj a) (Gobj b)} (Gfunct : Functor Gobj G)
  {Fobj : objC → objD} {F : ∀ {a b : objC}, homC a b → homD (Fobj a) (Fobj b)} (Ffunct : Functor Fobj F) :
  Functor (fun x : objC => Gobj (Fobj x))
          (fun {a b : objC} (f : homC a b) => G (F f)) where
  preserv_id a := by rw [Ffunct.preserv_id, Gfunct.preserv_id]
  preserv_comp f g := by rw [Ffunct.preserv_comp, Gfunct.preserv_comp]

infixr:80 " ● " => FunctComp

end FunctorLib
