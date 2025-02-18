Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Prod.
Require Import WildCat.NatTrans.


(** * A truncated bicategory has the same generating 2-cells as a bicategory but no relations between them.
      A truncated bicategory where all 2-cells are invertible is the same as a 1-category. *)
Class IsTruncatedBicat (A: Type) `{Is01Cat A} `{!Is2Graph A} := {
  is01cat_bicat_hom : forall (a b : A), Is01Cat (a $-> b);
  is0functor_bicat_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_bicat_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  bicat_assoc : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $-> h $o (g $o f);
  bicat_assoc_opp : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $-> (h $o g) $o f;
  bicat_idl : forall {a b : A} (f : a $-> b), Id b $o f $-> f;
  bicat_idl_opp : forall {a b : A} (f : a $-> b), f $-> Id b $o f ;
  bicat_idr : forall {a b : A} (f : a $-> b), f $o Id a $-> f;
  bicat_idr_opp : forall {a b : A} (f : a $-> b), f $-> f $o Id a;
}.

Existing Instance is01cat_bicat_hom.
Existing Instance is0functor_bicat_postcomp.
Existing Instance is0functor_bicat_precomp.

Declare Scope twocat_scope.
Notation "A $=> B" := (Hom (A:= Hom _ _) A B) : twocat_scope.
(* Vertical composition of 2-cells*)
Notation "g * f" := (cat_comp (A:=Hom _ _) g f) : twocat_scope.

Print Implicit bicat_assoc.
Notation "h $@L p" := (fmap (cat_postcomp _ h) p) : twocat_scope.
Notation "p $@R h" := (fmap (cat_precomp _ h) p) : twocat_scope.

Open Scope twocat_scope.
Print Implicit Is1Natural.
Class IsBicategory (A : Type) `{Is01Cat A} `{!Is2Graph A} `{!Is3Graph A} := {
  is_truncated_bicat: IsTruncatedBicat A;
  is1cat_2cells: forall (a b : A), Is1Cat (Hom a b);
  is1functor_bicat_postcomp : forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g);
  is1functor_bicat_precomp : forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;
  bifunctor_coh_comp : forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $=> f') (p' : g $=> g'),
    (g' $@L p) * (p' $@R f) $== (p' $@R f') * (g $@L p) ;
  bicat_assoc_inv: forall {a b c d} (f : a $->b) (g : b $-> c) (h : c $->d),
    Inverse (bicat_assoc f g h) (bicat_assoc_opp f g h);
  bicat_idl_inv : forall {a b} (f : a $-> b), Inverse (bicat_idl f) (bicat_idl_opp f);
  bicat_idr_inv : forall {a b} (f : a $-> b), Inverse (bicat_idr f) (bicat_idr_opp f);
  bicat_assoc_nat : forall {a b c d: A},
  Is1Natural
  (fun '(f , g , h ) => h $o g $o f)
  (fun '(f , g , h ) => h $o (g $o f))
  (fun '(f , g , h ) => bicat_assoc (a:=a)(b:=b)(c:=c)(d:=d) f g h)
}.

Close Scope twocat_scope.

(** * Wild (2,1)-categories *)
Class Is21Cat (A : Type) `{Is1Cat A, !Is3Graph A} :=
{
  is1cat_hom : forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_postcomp : forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) ;
  is1functor_precomp : forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) ;
  bifunctor_coh_comp : forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $== f') (p' : g $== g'),
    (p' $@R f) $@ (g' $@L p) $== (g $@L p) $@ (p' $@R f') ;

  (** Naturality of the associator in each variable separately *)
  is1natural_cat_assoc_l : forall (a b c d : A) (f : a $-> b) (g : b $-> c),
      Is1Natural (cat_precomp d f o cat_precomp d g) (cat_precomp d (g $o f))
                 (cat_assoc f g);
  is1natural_cat_assoc_m : forall (a b c d : A) (f : a $-> b) (h : c $-> d),
      Is1Natural (cat_precomp d f o cat_postcomp b h) (cat_postcomp a h o cat_precomp c f)
                 (fun g => cat_assoc f g h);
  is1natural_cat_assoc_r : forall (a b c d : A) (g : b $-> c) (h : c $-> d),
      Is1Natural (cat_postcomp a (h $o g)) (cat_postcomp a h o cat_postcomp a g)
                 (fun f => cat_assoc f g h);

  (** Naturality of the unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (cat_postcomp a (Id b)) idmap
                 cat_idl ;

  is1natural_cat_idr : forall (a b : A),
      Is1Natural (cat_precomp b (Id a)) idmap
                 cat_idr;

  (** Coherence *)
  cat_pentagon : forall (a b c d e : A)
                        (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L cat_assoc f g h) $o (cat_assoc f (h $o g) k) $o (cat_assoc g h k $@R f)
      $== (cat_assoc (g $o f) h k) $o (cat_assoc f g (k $o h)) ;

  cat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      (g $@L cat_idl f) $o (cat_assoc f (Id b) g) $== (cat_idr g $@R f)
}.

Global Existing Instance is1cat_hom.
Global Existing Instance is1gpd_hom.
Global Existing Instance is1functor_precomp.
Global Existing Instance is1functor_postcomp.
Global Existing Instance is1natural_cat_assoc_l.
Global Existing Instance is1natural_cat_assoc_m.
Global Existing Instance is1natural_cat_assoc_r.
Global Existing Instance is1natural_cat_idl.
Global Existing Instance is1natural_cat_idr.

(** *** Whiskering functoriality *)

Definition cat_postwhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : a $-> b} (k : b $-> c) (p : f $== g) (q : g $== h)
  : k $@L (p $@ q) $== (k $@L p) $@ (k $@L q).
Proof.
  rapply fmap_comp.
Defined.

Definition cat_prewhisker_pp {A} `{Is21Cat A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $== g) (q : g $== h)
  : (p $@ q) $@R k $== (p $@R k) $@ (q $@R k).
Proof.
  rapply fmap_comp.
Defined.

(** *** Exchange law *)

Definition cat_exchange {A : Type} `{Is21Cat A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $== f') (q : f' $== f'') (r : g $== g') (s : g' $== g'')
  : (p $@ q) $@@ (r $@ s) $== (p $@@ r) $@ (q $@@ s).
Proof.
  unfold "$@@".
  (** We use the distributivity of [$@R] and [$@L] in a (2,1)-category (since they are functors) to see that we have the same dadta on both sides of the 3-morphism. *)
  nrefine ((_ $@L cat_prewhisker_pp _ _ _ ) $@ _).
  nrefine ((cat_postwhisker_pp _ _ _ $@R _) $@ _).
  (** Now we reassociate and whisker on the left and right. *)
  nrefine (cat_assoc _ _ _ $@ _).
  refine (_ $@ (cat_assoc _ _ _)^$).
  nrefine (_ $@L _).
  refine (_ $@ cat_assoc _ _ _).
  refine ((cat_assoc _ _ _)^$ $@ _).
  nrefine (_ $@R _).
  (** Finally we are left with the bifunctoriality condition for left and right whiskering which is part of the data of the (2,1)-cat. *)
  apply bifunctor_coh_comp.
Defined.
