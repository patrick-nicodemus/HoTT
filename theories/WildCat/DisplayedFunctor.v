Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.Equivalences.
Require Import Types.Sigma.
Require Import WildCat.Core.
Require Import WildCat.Displayed.
Require Import WildCat.Equiv.
Require Import WildCat.FunctorCat.

Instance DisplayedFunctor_IsDGraph
  (A : Type) (DA : A -> Type) `{IsD1Cat A DA}
  (B : Type) (DB : B -> Type) `{IsD1Cat B DB} :
  @IsDGraph (Fun11 A B) _ (fun F => D1Functor F).
Proof.
  unfold IsDGraph.
  simpl.
  Check IsDGraph.
  constructor.
