Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Spaces.Nat
  HoTT.Spaces.Nat.Arithmetic
  HoTT.Spaces.Finite.Fin
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.DProp
  HoTT.BoundedSearch.

Local Open Scope nat_scope.

Definition FinNat (n : nat) : Type0 := {x : nat | x < n}.

Definition zero_finnat (n : nat) : FinNat n.+1
  := (0; leq_1_Sn).

Lemma path_zero_finnat (n : nat) (h : 0 < n.+1) : zero_finnat n = (0; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition succ_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1.+1; leq_S_n' u.1.+1 n u.2).
Check leq_S_n.

Lemma pred_finnat_subpf {n : nat} (j : nat) (p : j < n.+2) : pred j < n.+1.
  destruct j;  auto with nat.
Defined.

Definition pred_finnat {n : nat} (j : FinNat n.+2) : FinNat n.+1 :=
  (pred j.1; pred_finnat_subpf j.1 j.2).

Proposition sub_finnat_subpf {n : nat} (j : FinNat n) (k : nat) : j.1 - k < n.
Proof.
  destruct j; auto with nat.
Defined.

Definition sub_finnat {n : nat} (j : FinNat n) (k : nat) : FinNat n :=
  (j.1 - k; sub_finnat_subpf j k).
  
Lemma path_succ_finnat {n : nat} (u : FinNat n) (h : u.1.+1 < n.+1)
  : succ_finnat u = (u.1.+1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition last_finnat (n : nat) : FinNat n.+1
  := exist (fun x => x < n.+1) n (leq_refl n.+1).

Lemma path_last_finnat (n : nat) (h : n < n.+1)
  : last_finnat n = (n; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition incl_finnat {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1; leq_trans u.2 (leq_S n n (leq_n n))).

Lemma path_incl_finnat (n : nat) (u : FinNat n) (h : u.1 < n.+1)
  : incl_finnat u = (u.1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition finnat_ind (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : P n u.
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 u.1 u.2).
  - destruct u as [x h].
    destruct x as [| x].
    + exact (transport (P n.+1) (path_zero_finnat _ h) (z _)).
    + refine (transport (P n.+1) (path_succ_finnat (x; leq_S_n _ _ h) _) _).
      apply s. apply IHn.
Defined.

Lemma compute_finnat_ind_zero (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  (n : nat)
  : finnat_ind P z s (zero_finnat n) = z n.
Proof.
  cbn. by induction (hset_path2 1 (path_zero_finnat n leq_1_Sn)).
Defined.

Lemma compute_finnat_ind_succ (P : forall n : nat, FinNat n -> Type)
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n),
       P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : finnat_ind P z s (succ_finnat u) = s n u (finnat_ind P z s u).
Proof.
  refine
    (_ @ transport
          (fun p => transport _ p (s n u _) = s n u (finnat_ind P z s u))
          (hset_path2 1 (path_succ_finnat u (leq_S_n' _ _ u.2))) 1).
  destruct u as [u1 u2].
  assert (u2 = leq_S_n u1.+1 n (leq_S_n' u1.+1 n u2)) as p.
  - apply path_ishprop.
  - simpl. by induction p.
Defined.

Monomorphic Definition is_bounded_fin_to_nat {n} (k : Fin n)
  : fin_to_nat k < n.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + apply (@leq_trans _ n _).
      * apply IHn.
      * by apply leq_S.
    + apply leq_refl.
Defined.

Monomorphic Definition fin_to_finnat {n} (k : Fin n) : FinNat n
  := (fin_to_nat k; is_bounded_fin_to_nat k).

Monomorphic Fixpoint finnat_to_fin {n : nat} : FinNat n -> Fin n
  := match n with
     | 0 => fun u => Empty_rec (not_lt_n_0 _ u.2)
     | n.+1 => fun u =>
        match u with
        | (0; _) => fin_zero
        | (x.+1; h) => fsucc (finnat_to_fin (x; leq_S_n _ _ h))
        end
     end.

Lemma path_fin_to_finnat_fsucc {n : nat} (k : Fin n)
  : fin_to_finnat (fsucc k) = succ_finnat (fin_to_finnat k).
Proof.
  apply path_sigma_hprop.
  apply path_nat_fsucc.
Defined.

Lemma path_fin_to_finnat_fin_zero (n : nat)
  : fin_to_finnat (@fin_zero n) = zero_finnat n.
Proof.
  apply path_sigma_hprop.
  apply path_nat_fin_zero.
Defined.

Lemma path_fin_to_finnat_fin_incl {n : nat} (k : Fin n)
  : fin_to_finnat (fin_incl k) = incl_finnat (fin_to_finnat k).
Proof.
  reflexivity.
Defined.

Lemma path_fin_to_finnat_fin_last (n : nat)
  : fin_to_finnat (@fin_last n) = last_finnat n.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_succ {n : nat} (u : FinNat n)
  : finnat_to_fin (succ_finnat u) = fsucc (finnat_to_fin u).
Proof.
  cbn. do 2 f_ap. by apply path_sigma_hprop.
Defined.

Lemma path_finnat_to_fin_zero (n : nat)
  : finnat_to_fin (zero_finnat n) = fin_zero.
Proof.
  reflexivity.
Defined.

Lemma path_finnat_to_fin_incl {n : nat} (u : FinNat n)
  : finnat_to_fin (incl_finnat u) = fin_incl (finnat_to_fin u).
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 _ u.2).
  - destruct u as [x h].
    destruct x as [| x]; [reflexivity|].
    refine ((ap _ (ap _ (path_succ_finnat (x; leq_S_n _ _ h) h)))^ @ _).
    refine (_ @ ap fsucc (IHn (x; leq_S_n _ _ h))).
    by induction (path_finnat_to_fin_succ (incl_finnat (x; leq_S_n _ _ h))).
Defined.

Lemma path_finnat_to_fin_last (n : nat)
  : finnat_to_fin (last_finnat n) = fin_last.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - exact (ap fsucc IHn).
Defined.

Lemma path_finnat_to_fin_to_finnat {n : nat} (u : FinNat n)
  : fin_to_finnat (finnat_to_fin u) = u.
Proof.
  induction n as [| n IHn].
  - elim (not_lt_n_0 _ u.2).
  - destruct u as [x h].
    apply path_sigma_hprop.
    destruct x as [| x].
    + exact (ap pr1 (path_fin_to_finnat_fin_zero n)).
    + refine ((path_fin_to_finnat_fsucc _)..1 @ _).
      exact (ap S (IHn (x; leq_S_n _ _ h))..1).
Defined.

Lemma path_fin_to_finnat_to_fin {n : nat} (k : Fin n)
  : finnat_to_fin (fin_to_finnat k) = k.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + specialize (IHn k).
      refine (path_finnat_to_fin_incl (fin_to_finnat k) @ _).
      exact (ap fin_incl IHn).
    + apply path_finnat_to_fin_last.
Defined.

Definition equiv_fin_finnat (n : nat) : Fin n <~> FinNat n
  := equiv_adjointify fin_to_finnat finnat_to_fin
      path_finnat_to_fin_to_finnat
      path_fin_to_finnat_to_fin.


Local Definition nat_of_ord {n : nat} : FinNat n -> nat := pr1.
Coercion nat_of_ord : FinNat >-> nat.
Check Decidable.

Section finnat_well_founded.
  Context (n : nat).
  Context (P : FinNat n -> Type).
  Context (H : forall k : FinNat n, Decidable (P k)).

  Definition finnat_to_nat_predicate :=
    fun k : nat => match @leq_dichot k.+1 n with
                            | inl a => P (k ; a)
                            | inr _ => Empty
                   end.
  Local Notation P' := finnat_to_nat_predicate.

  Lemma to_nat_predicate_decidable : forall n : nat, Decidable (P' n).
  Proof.
    intro m; unfold P'; destruct leq_dichot; [ apply H | exact _ ]. 
  Defined.

  Local Lemma to_nat_predicate_equivalence : forall k, P k <-> P' k.1.
  Proof.
    intro k.
    assert (R: forall l : k.1 < n, k = (k.1 ; l)) by (intro l; apply (injective pr1); done).
    split; unfold P'; destruct leq_dichot; intro pf.
    - by destruct (R l).
    - destruct k; auto with nat.
    - by destruct (symmetric_paths _ _ (R l)).
    - by apply Empty_rect.
  Defined.
  
  Lemma hexists_iff_to_nat_predicate_hexists : (hexists P) <-> (hexists P').
  Proof.
    split; intro M; strip_truncations; apply tr.
    - destruct M as [x pf]. exists x.1. by apply to_nat_predicate_equivalence.
    - destruct M as [x pf]. unfold P' in pf. destruct leq_dichot in pf.
      + by exists (x; l).
                  + by apply Empty_rect.
  Defined.

  Locate merely_inhabited_iff_inhabited_decidable.
  Proposition finnat_well_founded (H' : hexists P)
    : { k : FinNat n & (P k * forall k' : FinNat n, P k' -> k <= k')%type }.
  Proof.
    assert (t := BoundedSearch.n_to_min_n P' to_nat_predicate_decidable).
    assert (X := (fst hexists_iff_to_nat_predicate_hexists) H').
    assert (z: BoundedSearch.min_n_Type P'). {
      assert (Q := ishpropmin_n P' X); strip_truncations.
      destruct X as [x pf]; apply (t x pf).
    }
    destruct z as [x [Px minimal]].
    assert (xbd : x < n). {
      strip_truncations.
      destruct H' as [[yval ybd] pf].
      apply (mixed_trans1 _ yval); [ | assumption ].
      apply minimal.
      by apply to_nat_predicate_equivalence in pf.
    }
    exists (x ; xbd); split.
    + apply merely_inhabited_iff_inhabited_stable.
      strip_truncations; apply tr.
      by apply to_nat_predicate_equivalence.
    + intros k' pfk'. strip_truncations.
      apply minimal. by apply to_nat_predicate_equivalence.
  Defined.

End finnat_well_founded.

Proposition cases_incl_last (n : nat) (Q : forall x : FinNat n.+1, Type) 
  : (forall k : FinNat n, Q (incl_finnat k)) -> Q (last_finnat n) -> forall k, Q k.
Proof.
  intros A B k.
  destruct k as [kval kbd].
  assert (kbd' := kbd). apply leq_S_n in kbd'. destruct kbd' as [ | m kbd'].
  - assert (RW: (kval; kbd) = (last_finnat kval)) by (now apply (path_sigma_hprop));
      destruct RW; assumption.
  - assert (RW: incl_finnat (kval; leq_S_n' _ _ kbd') = (kval ; kbd)) by
      (now apply (path_sigma_hprop)); destruct RW; auto.
Defined.

Proposition DeMorgan1 (n : nat) (P : forall k : FinNat n, Type) `{forall k, Decidable (P k)}
  : (~ forall x : FinNat n, P x) -> exists x : FinNat n, ~ P x.
Proof.
  induction n as [| n0];
    [ intro z; contradiction z; intro p; destruct p; auto with nat |].
  intro z. destruct (dec (P (last_finnat n0)));
    [ | exists (last_finnat n0); done ].
  set (P' := fun l : FinNat n0 => P (incl_finnat l)).
  specialize IHn0 with P'.
  cut ({x : FinNat n0 & ~ P' x});
    [ intros [x pfx]; exists (incl_finnat x); done |].
  apply (IHn0 _). 
  intro m. apply z.
  exact (cases_incl_last _ P m p).
Defined.

Proposition finnat_co_well_founded (n : nat) (P : FinNat n -> Type)
  (H : forall k, Decidable (P k)) (H' : ~ forall x, P x)
  : { k : FinNat n & (~ P k * forall k' : FinNat n, k < k' -> P k')%type }.
Proof.
  destruct n as [ |m]; [ contradiction H'; intros [xval xbd]; auto with nat |].
  set (Q := fun k : FinNat m.+1 => ~ P (sub_finnat (last_finnat m) k.1)).
  apply DeMorgan1 in H'; [ | done].
  assert (heq : hexists Q). {
    apply tr. destruct H' as [val pf].
    exists (sub_finnat (last_finnat m) val). unfold Q; simpl.
    assert (RW : val = (sub_finnat (last_finnat m) (m - val)) ). {
      apply (injective pr1); simpl.
      apply symmetry, ineq_sub; exact (leq_S_n _ _ val.2).
    } destruct RW; assumption.
  } 
  assert (EJ := finnat_well_founded _ Q _ heq); destruct EJ as [y [holds gtest]].
  exists (sub_finnat (last_finnat m) y.1); split; [ assumption |].
  intro k'; simpl; intro ineq.
  apply stable.
  intro ne. set (z := sub_finnat (last_finnat m) k').
  specialize gtest with z.
  unshelve refine (let M := gtest _ in _).
  { 
    assert (RW : k' = (sub_finnat (last_finnat m) z)). {
      apply path_sigma_hprop; symmetry; simpl; apply ineq_sub;
        destruct k' as [kval' kbd']. exact (leq_S_n _ _ kbd').
    }
    symmetry in RW; clearbody z; clear gtest ineq.
    destruct RW in ne; apply ne.
  } clearbody M; clear gtest.
  unfold z in M; simpl in M.
  apply natpmswap4 in ineq.
  apply (natpmswap3 _ ) in M;
    [ | destruct k' as [kval' kbd']; exact (leq_S_n _ _ kbd')].
  destruct (nat_add_comm k' y.1) in ineq.
  auto with nat.
Defined.
