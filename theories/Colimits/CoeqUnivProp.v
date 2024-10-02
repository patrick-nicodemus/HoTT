Require Import Basics.Overture.
Require Import Basics.Tactics.
Require Import Basics.PathGroupoids.
Require Import Types.Paths.
Require Import Colimits.Coeq.
Require Import Cubical.DPath.
Require Import Cubical.DPathSquare.
Require Import WildCat.Core.
Require Import WildCat.Displayed.
Require Import WildCat.Equiv.
Require Import WildCat.EquivGpd.
Require Import WildCat.Forall.
Require Import WildCat.NatTrans.
Require Import WildCat.Paths.
Require Import WildCat.ZeroGroupoid.

(** Using wild 0-groupoids, the universal property can be proven without funext. A simple equivalence of 0-groupoids between [Coeq f g -> P] and [{ h : A -> P & h o f == h o g }] would not carry all the higher-dimensional information, but if we generalize it to dependent functions, then it does suffice. *)
Section UnivProp.
  Context {B A : Type} (f g : B -> A) (P : Coeq f g -> Type).

  (** This allows Coq to infer 0-groupoid structures of the form [@isgraph_forall C P (fun c => isgraph_paths (P c))] on any type of the form [forall c, P c].  [isgraph_paths] is not a global instance.  [isgraph_total] is, but we need to adjust the priority.  The other needed ingredients are all global instances. *)
  Local Existing Instances isgraph_total | 1.
  Local Existing Instances isgraph_paths | 2.

  (** The codomain of the equivalence is a sigma-groupoid of this family. *)
  Definition Coeq_ind_data (h : forall a : A, P (coeq a))
    := forall b : B, DPath P (cglue b) (h (f b)) (h (g b)).

  (** We consider [Coeq_ind_data] to be a displayed 0-groupoid, where objects over [h : forall a : A, P (coeq a)] are dependent paths as defined above and morphisms over [p : h == k] are witnesses that p commutes with the homotopies over [h] and [k]. *)
  Local Instance isdgraph_Coeq_ind_data : IsDGraph Coeq_ind_data.
  Proof.
    intros h k p r s.
    exact (forall b, ap (transport P (cglue b)) (p (f b)) @ s b = r b @ p (g b)).
  Defined.

  Local Instance isd01cat_Coeq_ind_data : IsD01Cat Coeq_ind_data.
  Proof.
    nrapply Build_IsD01Cat.
    - intros h h' b; exact (concat_1p_p1 _).
    - intros h k j p q h' k' j' p' q' b.
      lhs nrapply ap_pp_p.
      lhs nrapply (whiskerL _ (p' b)).
      lhs nrapply concat_p_pp.
      lhs nrapply (whiskerR (q' b)).
      nrapply concat_pp_p.
  Defined.

  Local Instance isd0gpd_Coeq_ind_data : IsD0Gpd Coeq_ind_data.
  Proof.
    intros h k p r s p' b.
    lhs nrapply (whiskerR (ap_V _ _)).
    nrapply moveL_pV.
    lhs nrapply concat_pp_p.
    lhs nrapply (whiskerL _ (p' b)^).
    lhs nrapply concat_p_pp.
    lhs nrapply (whiskerR (concat_Vp _)).
    nrapply concat_1p.
  Defined.

  (** Here is the functor. The domain is the fully-applied type of [Coeq_ind]: sections of [P] over [Coeq f g]. The codomain consists of input data for [Coeq_ind] given a 0-groupoid structure via [is0gpd_total]. *)
  Definition Coeq_ind_inv : (forall z : Coeq f g, P z) -> sig Coeq_ind_data.
  Proof.
    intros h.
    exists (h o coeq).
    intros b.
    exact (apD h (cglue b)).
  Defined.

  (** Use [Set Printing Implicit] to see the 0-groupoid structures described above. *)
  Local Instance is0functor_Coeq_ind_inv : Is0Functor Coeq_ind_inv.
  Proof.
    nrapply Build_Is0Functor.
    intros h k p.
    exists (p o coeq).
    intros b.
    nrapply moveL_pM.
    exact ((apD_homotopic p (cglue b))^).
  Defined.

  Local Instance issurjinj_Coeq_ind_inv : IsSurjInj Coeq_ind_inv.
  Proof.
    nrapply Build_IsSurjInj.
    - intros [h r].
      exists (Coeq_ind P h r).
      exists (fun a => idpath).
      intros b.
      nrefine (concat_1p _ @ _ @ (concat_p1 _)^).
      symmetry.
      nrapply Coeq_ind_beta_cglue.
    - intros h k [p p'].
      snrapply Coeq_ind.
      1: exact p.
      intros b; specialize (p' b).
      lhs nrapply transport_paths_FlFr_D.
      lhs nrapply concat_pp_p.
      lhs nrapply (whiskerL _ p').
      lhs nrapply concat_p_pp.
      lhs nrapply (whiskerR (concat_Vp _)).
      nrapply concat_1p.
  Defined.

  Definition equiv_0gpd_Coeq_ind
    : Build_ZeroGpd (forall z : Coeq f g, P z) _ _ _
      $<~> Build_ZeroGpd (sig Coeq_ind_data) _ _ _.
  Proof.
    snrapply Build_CatEquiv.
    1: rapply Build_Morphism_0Gpd.
    rapply isequiv_0gpd_issurjinj.
  Defined.

End UnivProp.

Section UnivPropNat.
  Context {B A : Type} (f g : B -> A) {B' A' : Type} (f' g' : B' -> A')
    (h : B -> B') (k : A -> A') (p : k o f == f' o h) (q : k o g == g' o h)
    (P : Coeq f' g' -> Type).

  Local Open Scope dpath_scope.

  Local Existing Instances isgraph_total | 1.
  Local Existing Instances isgraph_paths | 2.
  Local Existing Instances isdgraph_Coeq_ind_data.

  Local Instance isgraph_Coeq_ind_data_total
    : IsGraph (sig (Coeq_ind_data f g (P o functor_coeq h k p q))).
  Proof.
    rapply isgraph_total.
  Defined.

  Definition functor_Coeq_ind_data
    : sig (Coeq_ind_data f' g' P)
      -> sig (Coeq_ind_data f g (P o functor_coeq h k p q)).
  Proof.
    unfold Coeq_ind_data in *.
    intros [m r].
    exists (m o k).
    intros b.
    apply (dp_compose' _ _ (functor_coeq_beta_cglue h k p q b)).
    nrefine (_ @Dp r (h b) @Dp _).
    1: exact (dp_compose coeq P (p b) (apD m (p b))).
    exact (dp_compose coeq P (q b)^ (apD m (q b)^)).
  Defined.

  (** Action of (Coeq_ind _ _ _ o functor_coeq) on the path (cglue b). *)
  Definition Coeq_ind_functor_coeq_beta_cglue {b m r}
    : apD (fun x => Coeq_ind P m r (functor_coeq h k p q x)) (cglue b)
      = (dp_compose' (functor_coeq h k p q) P (functor_coeq_beta_cglue h k p q b))^-1
          ((dp_compose coeq P (p b) (apD m (p b)) @Dp r (h b)) @Dp
          dp_compose coeq P (q b)^ (apD m (q b)^)).
  Proof.
    nrefine (ap _ _ @ (dp_apD_compose' _ _ _ (Coeq_ind P m r))^)^.
    lhs nrapply (dp_whiskerL _ (dp_apD_compose_inv coeq P (Coeq_ind P m r))^).
    lhs nrapply (dp_whiskerR _ (dp_whiskerR _ (dp_apD_compose_inv coeq P _)^)).
    lhs nrapply (dp_whiskerR _ (dp_whiskerL _ (Coeq_ind_beta_cglue _ _ _ _)^)).
    lhs nrapply (dp_whiskerR _ (dp_apD_pp _ _ _ _ _)^).
    exact (dp_apD_pp _ _ _ _ _)^.
  Defined.

  Local Instance is0functor_functor_Coeq_ind_data
    : Is0Functor functor_Coeq_ind_data.
  Proof.
    nrapply Build_Is0Functor.
    intros [m r] [n s] [u v].
    exists (u o k).
    intros b.
    lhs nrapply (whiskerL _ Coeq_ind_functor_coeq_beta_cglue^).
    rhs nrapply (whiskerR Coeq_ind_functor_coeq_beta_cglue^ _).
    nrapply moveL_Mp.
    lhs nrapply concat_p_pp.
    lhs nrefine (transport_paths_FlFr_D (cglue b) (Coeq_ind_homotopy P u v _))^.
    apply (ds_dp (Coeq_ind P m r o _) (Coeq_ind P n s o _) _ _ _).
    exact (dp_apD_nat (Coeq_ind_homotopy P u v o _) (cglue b)).
  Defined.

  Definition functor_Coeq_ind_type
    : (forall z : Coeq f' g', P z) -> forall z : Coeq f g, P (functor_coeq h k p q z)
    := fun x => x o functor_coeq h k p q.

  Local Instance is0functor_functor_Coeq_ind_type
    : Is0Functor functor_Coeq_ind_type.
  Proof.
    nrapply Build_Is0Functor.
    intros m n r.
    exact (r o functor_coeq h k p q).
  Defined.

  Definition Coeq_ind_inv_nat
    : Coeq_ind_inv f g (P o functor_coeq h k p q) o functor_Coeq_ind_type
      $=> functor_Coeq_ind_data o (Coeq_ind_inv f' g' P).
  Proof.
    intros m.
    exists (fun _ => idpath).
    intros b; simpl.
    lhs nrapply concat_1p; rhs nrapply concat_p1.
    rhs nrapply (dp_apD_compose' _ _ (functor_coeq_beta_cglue h k p q b) _).
    nrapply ap.
    nrefine (_ @ (dp_apD_pp _ _ _ _ _)^).
    rhs nrapply (dp_whiskerR _ (dp_apD_pp _ _ _ _ _)).
    lhs nrapply (dp_whiskerL _ (dp_apD_compose_inv _ _ _)^).
    exact (dp_whiskerR _ (dp_whiskerR _ (dp_apD_compose_inv _ _ _)^)).
  Defined.

End UnivPropNat.
