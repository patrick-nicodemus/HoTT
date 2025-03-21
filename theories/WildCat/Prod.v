Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import Types.Prod.

(** * Product categories *)

(** Products preserve (0,1)-categories. *)
Instance isgraph_prod A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A * B)
  := Build_IsGraph (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)).

Instance is01cat_prod A B `{Is01Cat A} `{Is01Cat B}
  : Is01Cat (A * B).
Proof.
  econstructor.
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

Instance is0gpd_prod A B `{Is0Gpd A} `{Is0Gpd B}
 : Is0Gpd (A * B).
Proof.
  srapply Build_Is0Gpd.
  intros [x1 x2] [y1 y2] [f1 f2].
  cbn in *.
  exact ( (f1^$, f2^$) ).
Defined.

Instance is2graph_prod A B `{Is2Graph A, Is2Graph B}
  : Is2Graph (A * B).
Proof.
  intros [x1 x2] [y1 y2].
  rapply isgraph_prod.
Defined.

Instance is1cat_prod A B `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (A * B).
Proof.
  srapply Build_Is1Cat.
  - intros [x1 x2] [y1 y2] [z1 z2] [h1 h2].
    srapply Build_Is0Functor.
    intros [f1 f2] [g1 g2] [p1 p2]; cbn in *.
    exact ( h1 $@L p1 , h2 $@L p2 ).
  - intros [x1 x2] [y1 y2] [z1 z2] [h1 h2].
    srapply Build_Is0Functor.
    intros [f1 f2] [g1 g2] [p1 p2]; cbn in *.
    exact ( p1 $@R h1 , p2 $@R h2 ).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *.
    exact(cat_assoc f1 g1 h1, cat_assoc f2 g2 h2).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *.
    exact(cat_assoc_opp f1 g1 h1, cat_assoc_opp f2 g2 h2).
  - intros [a1 a2] [b1 b2] [f1 f2].
    cbn in *.
    exact (cat_idl _, cat_idl _).
  - intros [a1 a2] [b1 b2] [g1 g2].
    cbn in *.
    exact (cat_idr _, cat_idr _).
Defined.

(** Product categories inherit equivalences *)

Instance hasequivs_prod A B `{HasEquivs A} `{HasEquivs B}
  : HasEquivs (A * B).
Proof.
  srefine (Build_HasEquivs (A * B) _ _ _ _
             (fun a b => (fst a $<~> fst b) * (snd a $<~> snd b))
             _ _ _ _ _ _ _ _ _).
  1:intros a b f; exact (CatIsEquiv (fst f) * CatIsEquiv (snd f)).
  all:cbn; intros a b f.
  - split; [ exact (fst f) | exact (snd f) ].
  - split; exact _.
  - intros [fe1 fe2]; split.
    + exact (Build_CatEquiv (fst f)).
    + exact (Build_CatEquiv (snd f)).
  - intros [fe1 fe2]; cbn; split; apply cate_buildequiv_fun.
  - split; [ exact ((fst f)^-1$) | exact ((snd f)^-1$) ].
  - split; apply cate_issect.
  - split; apply cate_isretr.
  - intros g r s; split.
    + exact (catie_adjointify (fst f) (fst g) (fst r) (fst s)).
    + exact (catie_adjointify (snd f) (snd g) (snd r) (snd s)).
Defined.

Instance isequivs_prod A B `{HasEquivs A} `{HasEquivs B}
       {a1 a2 : A} {b1 b2 : B} {f : a1 $-> a2} {g : b1 $-> b2}
       {ef : CatIsEquiv f} {eg : CatIsEquiv g}
  : @CatIsEquiv (A*B) _ _ _ _ _ (a1,b1) (a2,b2) (f,g) := (ef,eg).

(** ** Product functors *)

Instance is0functor_prod_functor {A B C D : Type}
  (F : A -> B) (G : C -> D) `{Is0Functor _ _ F, Is0Functor _ _ G}
  : Is0Functor (functor_prod F G).
Proof.
  apply Build_Is0Functor.
  intros [a1 c1] [a2 c2] [f g].
  exact (fmap F f , fmap G g).
Defined.

Instance is1functor_prod_functor {A B C D : Type}
  (F : A -> B) (G : C -> D) `{Is1Functor _ _ F, Is1Functor _ _ G}
  : Is1Functor (functor_prod F G).
Proof.
  apply Build_Is1Functor.
  - intros [a1 c1] [a2 c2] [f1 g1] [f2 g2] [p q].
    exact (fmap2 F p , fmap2 G q).
  - intros [a c].
    exact (fmap_id F a, fmap_id G c).
  - intros [a1 c1] [a2 c2] [a3 c3] [f1 g1] [f2 g2].
    exact (fmap_comp F f1 f2 , fmap_comp G g1 g2).
Defined.

Instance is0functor_fst {A B : Type} `{!IsGraph A, !IsGraph B}
  : Is0Functor (@fst A B).
Proof.
  apply Build_Is0Functor.
  intros ? ? f; exact (fst f).
Defined.

Instance is0functor_snd {A B : Type} `{!IsGraph A, !IsGraph B}
  : Is0Functor (@snd A B).
Proof.
  apply Build_Is0Functor.
  intros ? ? f; exact (snd f).
Defined.

(** Swap functor *)

Instance is0functor_equiv_prod_symm {A B : Type} `{IsGraph A, IsGraph B}
  : Is0Functor (equiv_prod_symm A B).
Proof.
  snapply Build_Is0Functor.
  intros a b.
  apply equiv_prod_symm.
Defined.

Instance is1functor_equiv_prod_symm {A B : Type} `{Is1Cat A, Is1Cat B}
  : Is1Functor (equiv_prod_symm A B).
Proof.
  snapply Build_Is1Functor.
  - intros a b f g.
    apply equiv_prod_symm.
  - intros a.
    reflexivity.
  - reflexivity.
Defined.

(** Inclusions into a product category are functorial. *)

Instance is0functor_prod_include10 {A B : Type} `{IsGraph A, Is01Cat B}
  (b : B)
  : Is0Functor (fun a : A => (a, b)).
Proof.
  napply Build_Is0Functor.
  intros a c f.
  exact (f, Id b).
Defined.

Instance is1functor_prod_include10 {A B : Type} `{Is1Cat A, Is1Cat B}
  (b : B)
  : Is1Functor (fun a : A => (a, b)).
Proof.
  napply Build_Is1Functor.
  - intros a c f g p.
    exact (p, Id _).
  - intros a; reflexivity.
  - intros a c d f g.
    exact (Id _, (cat_idl _)^$).
Defined.

Instance is0functor_prod_include01 {A B : Type} `{Is01Cat A, IsGraph B}
  (a : A)
  : Is0Functor (fun b : B => (a, b)).
Proof.
  napply Build_Is0Functor.
  intros b c f.
  exact (Id a, f).
Defined.

Instance is1functor_prod_include01 {A B : Type} `{Is1Cat A, Is1Cat B}
  (a : A)
  : Is1Functor (fun b : B => (a, b)).
Proof.
  napply Build_Is1Functor.
  - intros b c f g p.
    exact (Id _, p).
  - intros b; reflexivity.
  - intros b c d f g.
    exact ((cat_idl _)^$, Id _).
Defined.

(** Functors from a product category are functorial in each argument *)

Instance is0functor_functor_uncurried01 {A B C : Type}
  `{Is01Cat A, IsGraph B, IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (a : A)
  : Is0Functor (fun b => F (a, b))
  := is0functor_compose (fun b => (a, b)) F.

Instance is1functor_functor_uncurried01 {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (a : A)
  : Is1Functor (fun b => F (a, b))
  := is1functor_compose (fun b => (a, b)) F.

Instance is0functor_functor_uncurried10 {A B C : Type}
  `{IsGraph A, Is01Cat B, IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (b : B)
  : Is0Functor (fun a => F (a, b))
  := is0functor_compose (fun a => (a, b)) F.

Instance is1functor_functor_uncurried10 {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (b : B)
  : Is1Functor (fun a => F (a, b))
  := is1functor_compose (fun a => (a, b)) F.

(** Conversely, if [F : A * B -> C] is a 0-functor in each variable, then it is a 0-functor. *)
Definition is0functor_prod_is0functor {A B C : Type}
  `{IsGraph A, IsGraph B, Is01Cat C} (F : A * B -> C)
  `{!forall a, Is0Functor (fun b => F (a,b)), !forall b, Is0Functor (fun a => F (a,b))}
  : Is0Functor F.
Proof.
  snapply Build_Is0Functor.
  intros [a b] [a' b'] [f g].
  exact (fmap (fun a0 => F (a0,b')) f $o fmap (fun b0 => F (a,b0)) g).
Defined.
(** TODO: If we make this an instance, will it cause typeclass search to spin? *)
Hint Immediate is0functor_prod_is0functor : typeclass_instances.

(** And if [F : A * B -> C] is a 1-functor in each variable and satisfies a coherence, then it is a 1-functor. *)
Definition is1functor_prod_is1functor {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C} (F : A * B -> C)
  `{!forall a, Is0Functor (fun b => F (a,b)), !forall b, Is0Functor (fun a => F (a,b))}
  `{!forall a, Is1Functor (fun b => F (a,b)), !forall b, Is1Functor (fun a => F (a,b))}
  (bifunctor_coh : forall a0 a1 (f : a0 $-> a1) b0 b1 (g : b0 $-> b1),
    fmap (fun b => F (a1,b)) g $o fmap (fun a => F (a,b0)) f
      $== fmap (fun a => F(a,b1)) f $o fmap (fun b => F (a0,b)) g)
  : Is1Functor F.
Proof.
  snapply Build_Is1Functor.
  - intros [a b] [a' b'] [f g] [f' g'] [p p']; unfold fst, snd in * |- .
    exact (fmap2 (fun b0 => F (a,b0)) p' $@@ fmap2 (fun a0 => F (a0,b')) p).
  - intros [a b].
    exact ((fmap_id (fun b0 => F (a,b0)) b $@@ fmap_id (fun a0 => F (a0,b)) _) $@ cat_idr _).
  - intros [a b] [a' b'] [a'' b''] [f g] [f' g']; unfold fst, snd in * |- .
    refine ((fmap_comp (fun b0 => F (a,b0)) g g' $@@ fmap_comp (fun a0 => F (a0,b'')) f f') $@ _).
    nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ cat_assoc _ _ _).
    refine (cat_assoc _ _ _ $@ (_ $@L _^$) $@ cat_assoc_opp _ _ _).
    napply bifunctor_coh.
Defined.
Hint Immediate is1functor_prod_is1functor : typeclass_instances.

(** Applies a two variable functor via uncurrying. Note that the precondition on [C] is slightly weaker than that of [Bifunctor.fmap11]. *)
Definition fmap11_uncurry {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) {H2 : Is0Functor (uncurry F)}
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := @fmap _ _ _ _ (uncurry F) H2 (a0, b0) (a1, b1) (f, g).

Definition fmap_pair {A B C : Type}  
  `{IsGraph A, IsGraph B, IsGraph C}  
  (F : A * B -> C) `{!Is0Functor F}  
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} (g : b0 $-> b1)  
  : F (a0, b0) $-> F (a1, b1)  
  := fmap (a := (a0, b0)) (b := (a1, b1)) F (f, g).  

Definition fmap_pair_comp {A B C : Type}  
  `{Is1Cat A, Is1Cat B, Is1Cat C}  
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F}  
  {a0 a1 a2 : A} {b0 b1 b2 : B}
  (f : a0 $-> a1) (h : b0 $-> b1) (g : a1 $-> a2) (i : b1 $-> b2)  
  : fmap_pair F (g $o f) (i $o h)
    $== fmap_pair F g i $o fmap_pair F f h
  := fmap_comp (a := (a0, b0)) (b := (a1, b1)) (c := (a2, b2)) F (f, h) (g, i).

Definition fmap2_pair {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F}
  {a0 a1 : A} {f f' : a0 $-> a1} (p : f $== f')
  {b0 b1 : B} {g g' : b0 $-> b1} (q : g $== g')
  : fmap_pair F f g $== fmap_pair F f' g'
  := fmap2 F (a := (a0, b0)) (b := (a1, b1)) (f := (f, g)) (g := (f' ,g')) (p, q).
