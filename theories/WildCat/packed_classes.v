Require Import Basics.Overture Basics.Tactics.

Module Graph.
    Class class (A : Type) := {
        Hom : A -> A -> Type
    }.

    (* The type of graphs *)
    Record type := Pack {
        Ob : Type;
        class_of : class Ob
    }.
End Graph.

Notation Graph := Graph.type.
Notation Hom := Graph.Hom.
Notation IsGraph := Graph.class.

Coercion Graph.Ob : Graph >-> Sortclass.
Existing Instance Graph.class_of.
(* Print Implicit Graph.Hom. *)

Module ZeroOneCat.
    Record mixin (A : Graph) := {
        Id : forall (a:A), Hom a a;
        cat_comp : forall (a b c : A), Hom b c -> Hom a b -> Hom a c
    }.

    Class class (A : Type) := {
        isgraph : IsGraph A;
        is01cat : mixin (Graph.Pack A _)
    }.

    Record type := Pack {
        Ob : Type;
        class_of : class Ob
    }.
End ZeroOneCat.

Notation ZeroOneCat := ZeroOneCat.type.
